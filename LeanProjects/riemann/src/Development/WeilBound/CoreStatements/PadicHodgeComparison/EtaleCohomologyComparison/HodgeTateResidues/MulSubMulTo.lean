import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.RedPullPd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwAcrFromBase
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitsPullbackEmptyProductOne

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

universe w w' v u v' u'

namespace CrystallineSemistableComparison.HT

open PAlg

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ : R →+* R'}

theorem sub_mulTo (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F') (h) (c : R) (hc) (c' a : R') (hc') (e : σ c = a * c')
    (j : ℕ) (y : CH.H F j) :
    (subMor m S S' h).pull j ((mulTo c S hc).pull j y) = a • (mulTo c' S' hc').pull j (m.pull j y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change m.τ _ (c • z.1 (s ⋙ m.G)) = a • c' • m.τ _ (z.1 (s ⋙ m.G))
  rw [LinearMap.map_smulₛₗ, e, mul_smul]

theorem sub_mulSub (m : CH.Mor F F' σ) (S₁ S₂ : CH.SubF F) (S₁' S₂' : CH.SubF F') (h₁ h₂) (c : R) (hc) (c' : R') (hc') (e : σ c = c')
    (j : ℕ) (y : CH.H S₁.fn j) :
    (subMor m S₂ S₂' h₂).pull j ((mulSub c S₁ S₂ hc).pull j y) = (mulSub c' S₁' S₂' hc').pull j ((subMor m S₁ S₁' h₁).pull j y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change m.τ _ (c • (show S₁.S _ from z.1 (s ⋙ m.G)).1) = c' • m.τ _ (show S₁.S _ from z.1 (s ⋙ m.G)).1
  rw [LinearMap.map_smulₛₗ, e]

theorem mulSub_mulTo (S S' : CH.SubF F) (c c' c'' : R) (h h' h'') (e : c' * c = c'') (j : ℕ) (y : CH.H F j) :
    (mulSub c' S S' h').pull j ((mulTo c S h).pull j y) = (mulTo c'' S' h'').pull j y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change c' • c • z.1 s = c'' • z.1 s
  rw [smul_smul, e]

theorem sub_square {C₁ C₂ C₃ C₄ : Type 1} [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{0} R} {F₂ : C₂ ⥤ ModuleCat.{0} R} {F₃ : C₃ ⥤ ModuleCat.{0} R} {F₄ : C₄ ⥤ ModuleCat.{0} R}
    {σ₁ σ₂ σ₃ σ₄ : R →+* R} (τ : R →+* R) [RingHomCompTriple σ₁ σ₂ τ] [RingHomCompTriple σ₃ σ₄ τ]
    (m : CH.Mor F₁ F₂ σ₁) (b : CH.Mor F₂ F₃ σ₂) (b' : CH.Mor F₁ F₄ σ₃) (q : CH.Mor F₄ F₃ σ₄)
    (S₁ : CH.SubF F₁) (S₂ : CH.SubF F₂) (S₃ : CH.SubF F₃) (S₄ : CH.SubF F₄) (hm hb hb' hq)
    (η : b.G ⋙ m.G ⟶ q.G ⋙ b'.G)
    (hτ : ∀ T x, q.τ T (b'.τ (q.G.obj T) ((F₁.map (η.app T)).hom x)) = b.τ T (m.τ (b.G.obj T) x)) (n : ℕ) (x : CH.H S₁.fn n) :
    (subMor b S₂ S₃ hb).pull n ((subMor m S₁ S₂ hm).pull n x) = (subMor q S₄ S₃ hq).pull n ((subMor b' S₁ S₄ hb').pull n x) := by
  rw [pull_pull τ, pull_pull τ]
  exact CrystallineSemistableComparison.P.prism ((subMor m S₁ S₂ hm).comp (σ'' := τ) (subMor b S₂ S₃ hb))
    ((subMor b' S₁ S₄ hb').comp (σ'' := τ) (subMor q S₄ S₃ hq)) η (fun T x => Subtype.ext (hτ T x.1)) n x

end Gen

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section P
variable (ht : TFil l) (P : PAlg l ⥤ Type)

def shT {r r' : ℕ} (k : ℕ) (h : r + k = r') (n : ℕ) : CH.Mor (TT P r n).fn (TT P r' n).fn (RingHom.id _) :=
  mulSub (tA l ^ k) (TT P r n) (TT P r' n) fun T (x : T.1.obj.Acr n) hx => mem_TT.2 (by
    have := dividedPowerFiltration_pow_mul (B.DD false T.1.obj n) (ht T.1.obj n) h (mem_TT.1 hx)
    rw [← map_pow] at this
    exact this)

theorem shT_tMor {r r' : ℕ} (k : ℕ) (h : r + k = r') (n j : ℕ) (y : MH P n j) :
    (shT ht P k h n).pull j ((tMor ht P r n).pull j y) = (tMor ht P r' n).pull j y :=
  mulSub_mulTo (TT P r n) (TT P r' n) (tA l ^ r) (tA l ^ k) (tA l ^ r') _ _ _ (by rw [← pow_add, add_comm, h]) j y

variable {P}

def galT (σ : Gal(PadicAlgCl l/K)) (a : P ⟶ twF σ ⋙ P) (r n : ℕ) : CH.Mor (TT P r n).fn (TT P r n).fn (ACris.galCris σ) :=
  subMor (galMor σ a n) (TT P r n) (TT P r n) fun T x hx =>
    mem_TT.2 (Pb.dividedPowerFiltration_map (GlobalTheory.CompanionTheory.BetaGal.dd_twAcr false σ T.1.obj n) r ((mem_TT (T := (elTw σ a).obj T)).1 hx))

theorem galT_tMor (σ : Gal(PadicAlgCl l/K)) (a : P ⟶ twF σ ⋙ P) (r n j : ℕ) (y : MH P n j) :
    (galT σ a r n).pull j ((tMor ht P r n).pull j y) = χA σ ^ r • (tMor ht P r n).pull j ((galMor σ a n).pull j y) :=
  sub_mulTo (galMor σ a n) (TT P r n) (TT P r n) _ (tA l ^ r) _ (tA l ^ r) (χA σ ^ r) _
    (by rw [map_pow, galCris_tA, mul_pow]) j y

def pullT' {P' : PAlg l ⥤ Type} (u : P ⟶ P') (r n : ℕ) : CH.Mor (TT P' r n).fn (TT P r n).fn (RingHom.id _) :=
  subMor (pullMor u n) (TT P' r n) (TT P r n) fun T x hx => mem_TT.2 ((mem_TT (T := (elMap u).obj T)).1 hx)

theorem pullT_tMor {P' : PAlg l ⥤ Type} (u : P ⟶ P') (r n j : ℕ) (y : MH P' n j) :
    (pullT' u r n).pull j ((tMor ht P' r n).pull j y) = (tMor ht P r n).pull j ((pullMor u n).pull j y) :=
  (sub_mulTo (pullMor u n) (TT P' r n) (TT P r n) _ (tA l ^ r) _ (tA l ^ r) 1 _ (one_mul _).symm j y).trans (one_smul _ _)

end P

section F
variable {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l)

theorem β_sh (ht : TFil l) {r r' : ℕ} (k : ℕ) (h : r + k = r') (n j : ℕ)
    (x : CH.H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn j) :
    (βMorF F κ r' n).pull j ((pdSh (B.Lc F κ false n) ((base l).cris n) (ht (base l) n) k h).pull j x) =
      (shT ht (F.pt κ) k h n).pull j ((βMorF F κ r n).pull j x) :=
  sub_mulSub (B.βMor F κ false n) (B.pdS (B.Lc F κ false n) ((base l).cris n) r) (B.pdS (B.Lc F κ false n) ((base l).cris n) r')
    (TT (F.pt κ) r n) (TT (F.pt κ) r' n) _ _ (tA l ^ k) _ (tA l ^ k) _ rfl j x

theorem β_galF (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (r n j : ℕ)
    (x : CH.H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn j) :
    (βMorF F κ r n).pull j ((pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r).pull j x) =
      (galT σ (B.ptTw F κ σ hσ) r n).pull j ((βMorF F κ r n).pull j x) := by
  have h1 := pull_pull (ACris.galCris σ) (pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r)
    (βMorF F κ r n) j x
  have h2 := pull_pull (ACris.galCris σ) (βMorF F κ r n) (galT σ (B.ptTw F κ σ hσ) r n) j x
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact (pd_pull_eq ((βMorF F κ r n).comp (σ'' := ACris.galCris σ) (galT σ (B.ptTw F κ σ hσ) r n))
    ((pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r).comp (σ'' := ACris.galCris σ) (βMorF F κ r n))
    (GlobalTheory.CompanionTheory.BetaGal.etaGal F κ σ hσ false n) (fun f x => twAcr_mapAcr σ f.1.hom n x) (fun _ _ _ _ => rfl) j x).symm

variable {F} {F' : B.Fn O}

theorem β_pullF (u : B.Fn.Map F F') (r n j : ℕ) (x : CH.H (B.pdS (B.Lc F' κ false n) ((base l).cris n) r).fn j) :
    (βMorF F κ r n).pull j ((pdOm (CrystallineSemistableComparison.SH.pullM κ u false n) (RingHom.id _) (CrystallineSemistableComparison.SH.idc _) r).pull j x) =
      (pullT' (u.pt κ) r n).pull j ((βMorF F' κ r n).pull j x) :=
  sub_square (RingHom.id _) (B.pullMorC κ u false n) (B.βMor F κ false n) (B.βMor F' κ false n) (pullMor (u.pt κ) n)
    (B.pdS (B.Lc F' κ false n) ((base l).cris n) r) (B.pdS (B.Lc F κ false n) ((base l).cris n) r) (TT (F.pt κ) r n) (TT (F'.pt κ) r n)
    _ _ _ _ (GlobalTheory.CompanionTheory.BetaPull.cmpNat κ u false n) (fun _ _ => rfl) j x

end F

end CrystallineSemistableComparison.HT
