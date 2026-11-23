import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris Formalism.Per6

universe w w' v u v' u'

namespace CrystallineSemistableComparison.HT.Red

open CH PAlg B

section Gen
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R}

theorem sub_mulSub (m : CH.Mor F F' (RingHom.id R)) (c : R) (S₁ S₂ : SubF F) (S₁' S₂' : SubF F') (h₁ h₂ k k') (j : ℕ) (x : H S₁.fn j) :
    (subMor m S₂ S₂' h₂).pull j ((mulSub c S₁ S₂ k).pull j x) = (mulSub c S₁' S₂' k').pull j ((subMor m S₁ S₁' h₁).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (map_smul (m.τ _) c _)))

theorem sub_mulTo (m : CH.Mor F F' (RingHom.id R)) (c : R) (S : SubF F) (S' : SubF F') (h k k') (j : ℕ) (x : H F j) :
    (subMor m S S' h).pull j ((mulTo c S k).pull j x) = (mulTo c S' k').pull j (m.pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (map_smul (m.τ _) c _)))

theorem mulSub_mulTo (c c' c'' : R) (e : c'' = c' * c) (S S' : SubF F) (k k' k'') (j : ℕ) (x : H F j) :
    (mulSub c' S S' k').pull j ((mulTo c S k).pull j x) = (mulTo c'' S' k'').pull j x := by
  subst e
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (mul_smul c' c _).symm))

end Gen

section Pd
variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {Λ : Type} [CommRing Λ] {c : Λ →+* b.R} {c' : Λ →+* b'.R} {σ : b.R →+* b'.R}

theorem om_sh (m : GlobalTheory.LogCris.Mor L L' σ) (h : ∀ a, σ (c a) = c' (RingHom.id Λ a)) {t : Λ} (ht : c t ∈ b.I) (ht' : c' t ∈ b'.I)
    {r r' : ℕ} (k : ℕ) (e : r + k = r') (j : ℕ) (x : H (pdS L c r).fn j) :
    (pdOm m (RingHom.id Λ) h r').pull j ((pdSh L c ht k e).pull j x) =
      (pdSh L' c' ht' k e).pull j ((pdOm m (RingHom.id Λ) h r).pull j x) :=
  sub_mulSub (omMor m (RingHom.id Λ) h) (t ^ k) _ _ _ _ _ _ _ _ j x

end Pd

section PdCr
variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem cr_pull_eq' {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {σ : Λ →+* Λ'} {C' : Type u} [Category.{v} C']
    {F' : C' ⥤ ModuleCat.{w} Λ'} (r : ℕ) (m m' : CH.Mor (pdS (F.cr b ht κ) c r).fn F' σ) (η : ∀ T, m.G.obj T ⟶ m'.G.obj T)
    (nat : ∀ {T T' : C'} (f : T ⟶ T') (x : (m.G.obj T).B), (η T').φ ((m.G.map f).φ x) = (m'.G.map f).φ ((η T).φ x))
    (hτ : ∀ (T : C') x, m'.τ T (((pdS (F.cr b ht κ) c r).fn.map (η T)).hom x) = m.τ T x) (n : ℕ) (x : H (pdS (F.cr b ht κ) c r).fn n) :
    m.pull n x = m'.pull n x :=
  CrystallineSemistableComparison.P.prism m m' ⟨η, fun _ _ f => Thick.Hom.ext (RingHom.ext (nat f)) (funext fun j => j.elim)⟩ hτ n x

end PdCr

theorem map_eq (P : CommRingCat.{0} ⥤ Type) {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) (h : A →+* C) (e : g.comp f = h) (y : P.obj (CommRingCat.of A)) :
    P.map (CommRingCat.ofHom g) (P.map (CommRingCat.ofHom f) y) = P.map (CommRingCat.ofHom h) y := by
  rw [← Functor.map_comp_apply, ← CommRingCat.ofHom_comp, e]

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def redT (P : PAlg l ⥤ Type) (r n : ℕ) : CH.Mor (TT P r (n + 1)).fn (TT P r n).fn (RingHom.id _) :=
  subMor (CH.Mor.ofNatTrans (redEl P n.le_succ)) _ _ fun T x hx =>
    mem_TT.2 (Pb.dividedPowerFiltration_map (dd_red false T.1.obj n.le_succ) r (mem_TT.1 hx))

theorem reduction_commutes_tMor (ht : TFil l) (P : PAlg l ⥤ Type) (r n j : ℕ) (y : MH P (n + 1) j) :
    (redT P r n).pull j ((tMor ht P r (n + 1)).pull j y) = (tMor ht P r n).pull j ((MSys P j).r n y) :=
  sub_mulTo (CH.Mor.ofNatTrans (redEl P n.le_succ)) (tA l ^ r) _ _ _ _ _ j y

theorem red_uJ (k : Bool) (A : PAlg l) {m n : ℕ} (h : n ≤ m) (hle : JJ k A m ≤ (JJ k A n).comap (A.red h)) :
    (Ideal.quotientMap _ (A.red h) hle).comp (uJ k A m) = uJ k A n :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem red_comm (A : PAlg l) {m n : ℕ} (h : n ≤ m) (r : (base l).Acr m) :
    A.red h (mapAcr A.fromBase m r) = mapAcr A.fromBase n ((base l).red h r) :=
  PdOk.red_acr (pdOk_hom A.fromBase) h r

def redTh (n : ℕ) (T : El (F.pt κ)) :
    (gT F κ false (n + 1)).obj T ⟶ (SH.redM F κ false n).functor.obj ((gT F κ false n).obj T) :=
  crHom (T := gObj F κ false (n + 1) ((jE _).obj T)) (T' := (SH.redM F κ false n).obj (gObj F κ false n ((jE _).obj T)))
    (T.1.obj.red n.le_succ) (red_comm T.1.obj n.le_succ) (dd_red false T.1.obj n.le_succ)
    fun h => map_eq F.Pt _ _ _ (red_uJ false T.1.obj n.le_succ h) T.2.1

theorem β_red (r n j : ℕ) (x : H (pdS (Lc F κ false (n + 1)) ((base l).cris (n + 1)) r).fn j) :
    (βMorF F κ r n).pull j ((pdOm (SH.redM F κ false n) (RingHom.id _) (red_cris _ n.le_succ) r).pull j x) =
      (redT (F.pt κ) r n).pull j ((βMorF F κ r (n + 1)).pull j x) :=
  ((pull_pull (RingHom.id _) (pdOm (SH.redM F κ false n) (RingHom.id _) (red_cris _ n.le_succ) r) (βMorF F κ r n) j x).trans
    (cr_pull_eq' r ((βMorF F κ r (n + 1)).comp (redT (F.pt κ) r n))
      ((pdOm (SH.redM F κ false n) (RingHom.id _) (red_cris _ n.le_succ) r).comp (βMorF F κ r n)) (redTh F κ n)
      (fun f x => PdOk.red_acr (pdOk_hom f.1.hom) n.le_succ x) (fun T x => rfl) j x).symm).trans
    (pull_pull (RingHom.id _) (βMorF F κ r (n + 1)) (redT (F.pt κ) r n) j x).symm

theorem tt_mul (ht : TFil l) (P : PAlg l ⥤ Type) {r r' : ℕ} (k : ℕ) (e : r + k = r') (n : ℕ) (T : El P)
    (x : (modF (AcrEl P n)).obj T) (hx : x ∈ (TT P r n).S T) : tA l ^ k • x ∈ (TT P r' n).S T := by
  have := dividedPowerFiltration_pow_mul (DD false T.1.obj n) (ht T.1.obj n) e (mem_TT.1 hx)
  rw [← map_pow] at this
  exact mem_TT.2 this

theorem β_sh (ht : TFil l) {r r' : ℕ} (k : ℕ) (e : r + k = r') (n j : ℕ) (x : H (pdS (Lc F κ false n) ((base l).cris n) r).fn j)
    (y : MH (F.pt κ) n j) (h : (βMorF F κ r n).pull j x = (tMor ht (F.pt κ) r n).pull j y) :
    (βMorF F κ r' n).pull j ((pdSh (Lc F κ false n) ((base l).cris n) (ht (base l) n) k e).pull j x) =
      (tMor ht (F.pt κ) r' n).pull j y :=
  (sub_mulSub (βMor F κ false n) (tA l ^ k) _ _ _ _ _ _ _ (tt_mul ht (F.pt κ) k e n) j x).trans
    ((congrArg ((mulSub (tA l ^ k) (TT (F.pt κ) r n) (TT (F.pt κ) r' n) (tt_mul ht (F.pt κ) k e n)).pull j) h).trans
      (mulSub_mulTo (tA l ^ r) (tA l ^ k) (tA l ^ r') (by rw [← e, add_comm, pow_add]) _ _ _ _ _ j y))

end CrystallineSemistableComparison.HT.Red
