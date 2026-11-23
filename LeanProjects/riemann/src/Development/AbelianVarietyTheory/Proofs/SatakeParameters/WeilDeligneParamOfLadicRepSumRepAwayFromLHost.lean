import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent

namespace GlobalTheory.WeilDeligne.SumParam

section Blocks

variable (k : Type) [CommRing k] (a b : ℕ)

def blk : Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k →+*
    Matrix (Fin (a + b)) (Fin (a + b)) k :=
  (Matrix.reindexAlgEquiv k k finSumFinEquiv).toRingEquiv.toRingHom.comp
    { toFun := fun p => Matrix.fromBlocks p.1 0 0 p.2
      map_one' := Matrix.fromBlocks_one
      map_mul' := fun p q => by simp [Matrix.fromBlocks_multiply]
      map_zero' := by simp
      map_add' := fun p q => by simp [Matrix.fromBlocks_add] }

variable {k a b}

theorem blk_apply (p : Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k) :
    blk k a b p = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p.1 0 0 p.2) :=
  rfl

theorem blk_smul (c : k) (p : Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k) :
    blk k a b (c • p) = c • blk k a b p := by
  rw [blk_apply, blk_apply]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, Prod.smul_fst,
    Prod.smul_snd]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

theorem coe_sumRep {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      blk k a b ((ρ g : Matrix (Fin a) (Fin a) k), (ρ' g : Matrix (Fin b) (Fin b) k)) :=
  rfl

end Blocks

theorem isNilpotent_pair {R S : Type*} [MonoidWithZero R] [MonoidWithZero S] {x : R} {y : S}
    (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x, y) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  exact ⟨m + n, Prod.ext (by simp [pow_add, hm]) (by simp [pow_add, hn])⟩

theorem exp_pair {R S : Type*} [Ring R] [Ring S] [Module ℚ R] [Module ℚ S] {x : R} {y : S}
    (hx : IsNilpotent x) (hy : IsNilpotent y) : exp (x, y) = (exp x, exp y) := by
  have hp := isNilpotent_pair hx hy
  exact Prod.ext (map_exp hp (RingHom.fst R S)) (map_exp hp (RingHom.snd R S))

def eqv (a b : ℕ) : ((Fin a → ℂ) × (Fin b → ℂ)) ≃ₗ[ℂ] (Fin (a + b) → ℂ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℂ ℂ).symm.trans
    (LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm)

theorem eqv_toEndC {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a b : ℕ}
    (M : Matrix (Fin a) (Fin a) (Qbar l)) (M' : Matrix (Fin b) (Fin b) (Qbar l))
    (v : (Fin a → ℂ) × (Fin b → ℂ)) :
    eqv a b ((toEndC ι M).prodMap (toEndC ι M') v) = toEndC ι (blk _ a b (M, M')) (eqv a b v) := by
  obtain ⟨v1, v2⟩ := v
  funext i
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective i
  simp only [eqv, LinearEquiv.trans_apply, toEndC_apply, blk_apply, Matrix.reindex_apply,
    Matrix.toLin'_apply, LinearMap.prodMap_apply, LinearEquiv.funCongrLeft_apply]
  rw [← Matrix.submatrix_map, Matrix.submatrix_mulVec_equiv]
  rcases k with k | k <;> simp [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Function.comp_def,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {l : ℕ} [Fact l.Prime] {a b : ℕ}

theorem isMonodromy_sum {t : Ine (F := E) A →* Multiplicative ℤ_[l]}
    {ρ : G E Ω →* GL (Fin a) (Qbar l)} {ρ' : G E Ω →* GL (Fin b) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {N' : Matrix (Fin b) (Fin b) (Qbar l)}
    (hN : IsMonodromy t ρ N) (hN' : IsMonodromy t ρ' N') :
    IsMonodromy t (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') (blk _ a b (N, N')) := by
  obtain ⟨h1, U, hU, H⟩ := hN
  obtain ⟨h1', U', hU', H'⟩ := hN'
  have hp := isNilpotent_pair h1 h1'
  refine ⟨hp.map _, U ⊓ U', hU.inter hU', fun σ hσ => ?_⟩
  rw [coe_sumRep, H σ hσ.1, H' σ hσ.2, ← blk_smul, ← map_exp (hp.smul _), Prod.smul_mk,
    exp_pair (h1.smul _) (h1'.smul _)]

theorem wdMat_sum {t : Ine (F := E) A →* Multiplicative ℤ_[l]} {φ : Weil h} (hφ : deg φ = 1)
    {ρ : G E Ω →* GL (Fin a) (Qbar l)} {ρ' : G E Ω →* GL (Fin b) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {N' : Matrix (Fin b) (Fin b) (Qbar l)}
    (h1 : IsNilpotent N) (h1' : IsNilpotent N') (g : Weil h) :
    wdMat t hφ (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') (blk _ a b (N, N')) g =
      blk _ a b (wdMat t hφ ρ N g, wdMat t hφ ρ' N' g) := by
  have hp := isNilpotent_pair h1 h1'
  rw [wdMat, wdMat, wdMat, coe_sumRep, ← blk_smul, ← map_exp (hp.smul _), ← map_mul, Prod.smul_mk,
    exp_pair (h1.smul _) (h1'.smul _)]
  rfl

theorem isFrobSS_sum {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    {ρ₁ : Weil h → Module.End ℂ V} {N₁ : Module.End ℂ V} {x : WDRep h V}
    {ρ₂ : Weil h → Module.End ℂ V'} {N₂ : Module.End ℂ V'} {y : WDRep h V'}
    (hx : IsFrobSS ρ₁ N₁ x) (hy : IsFrobSS ρ₂ N₂ y) :
    IsFrobSS (fun g => (ρ₁ g).prodMap (ρ₂ g)) (N₁.prodMap N₂) (x.sum y) := by
  refine ⟨by rw [WDRep.sum_N, hx.1, hy.1], fun g => ⟨?_, ?_⟩⟩
  · rw [WDRep.sum_ρ]
    have hc : Commute ((x.ρ g, y.ρ g) : Module.End ℂ V × Module.End ℂ V') (ρ₁ g, ρ₂ g) :=
      Prod.ext (hx.2 g).1.eq (hy.2 g).1.eq
    exact hc.map (LinearMap.prodMapRingHom ℂ V V')
  · rw [WDRep.sum_ρ]
    have hn := (isNilpotent_pair (hx.2 g).2 (hy.2 g).2).map (LinearMap.prodMapRingHom ℂ V V')
    have e : (ρ₁ g).prodMap (ρ₂ g) - (x.ρ g).prodMap (y.ρ g) =
        LinearMap.prodMapRingHom ℂ V V' (ρ₁ g - x.ρ g, ρ₂ g - y.ρ g) := by
      rw [← Prod.mk_sub_mk, map_sub]; rfl
    show IsNilpotent ((ρ₁ g).prodMap (ρ₂ g) - (x.ρ g).prodMap (y.ρ g))
    rw [e]; exact hn

theorem wdOf_sumRep (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ)
    (ρ : G E Ω →* GL (Fin a) (Qbar l)) (ρ' : G E Ω →* GL (Fin b) (Qbar l))
    (hc : Continuous fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)))
    (hc' : Continuous fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))) :
    wdOf h hl ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') = (wdOf h hl ι ρ).lpSum (wdOf h hl ι ρ') := by
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hc
  obtain ⟨N', hN'⟩ := exists_isMonodromy h hl ht hc'
  have hS := isMonodromy_sum hN hN'
  obtain ⟨x, hx⟩ := hN.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  obtain ⟨y, hy⟩ := hN'.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  obtain ⟨z, hz⟩ := hS.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  rw [IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, N, x, hN, hx, rfl⟩,
    IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, N', y, hN', hy, rfl⟩,
    IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, _, z, hS, hz, rfl⟩, WD.lpSum_mk]
  refine (WD.sound ((isFrobSS_sum hx hy).iso hz (eqv a b) (fun g v => ?_) fun v => ?_)).symm
  · rw [wdMat_sum deg_frob hN.1 hN'.1]
    exact eqv_toEndC ι _ _ v
  · exact eqv_toEndC ι _ _ v

end GlobalTheory.WeilDeligne.SumParam

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.WeilDeligne.wdOf_sumRep_awayFrom : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a b : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l)) (w : PlE D.host) (hw : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))) → GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') = (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ).lpSum (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ') :=
  fun D l _ ι a b ρ ρ' w hw hc hc' =>
    GlobalTheory.WeilDeligne.SumParam.wdOf_sumRep (h := D.nd.plOm.2 w) hw ι ρ ρ' hc hc'
