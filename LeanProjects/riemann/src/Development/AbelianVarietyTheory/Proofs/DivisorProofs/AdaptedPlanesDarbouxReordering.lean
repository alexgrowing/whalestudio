import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictionAndProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosHomApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAdaptedDecomp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensAddRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensAdapted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotProductSplitBlocks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrLocalOfActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatPosIndicatorMemSB
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv
open scoped GlobalTheory.VacAny

namespace GlobalTheory.ThK.AdaptEv.VacuumBlock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_of_mem {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
    {Bf : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (AE F E) → AF F} {κ : Type} [Fintype κ]
    (co : Darboux Bf κ) (v : Pl F) :
    ∀ γ ∈ latAtV X W v, ∀ k, At (evFin F v) ((co.e γ).1 k) ∧ At (evFin F v) ((co.e γ).2 k) := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, x, -, y, -, rfl⟩ := hz
    intro k
    rw [map_smul]
    exact ⟨GlobalTheory.VacAny.at_mul_right ha _, GlobalTheory.VacAny.at_mul_right ha _⟩
  | zero =>
    intro k
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
    exact ⟨GlobalTheory.VacAny.at_zero, GlobalTheory.VacAny.at_zero⟩
  | add x y _ _ hx hy =>
    intro k
    rw [map_add]
    exact ⟨GlobalTheory.VacAny.at_add (hx k).1 (hy k).1, GlobalTheory.VacAny.at_add (hx k).2 (hy k).2⟩
  | neg x _ hx =>
    intro k
    rw [map_neg]
    exact ⟨GlobalTheory.VacAny.at_neg (hx k).1, GlobalTheory.VacAny.at_neg (hx k).2⟩

theorem psi_symp_eq_one {σ : E →ₐ[F] E} (B : Base F E) (hB : B.IsGood σ) {n d : ℕ} (X : Spc F E n) (W : Spc F E d)
    (r s r' s' : ℕ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)) (v : Pl F) :
    ∀ γ ∈ latAtV X W v, ∀ γ' ∈ latAtV X W v,
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) γ γ') = 1 := by
  intro γ hγ γ' hγ'
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_int_add_conj_eq_one_of_base_good B hB
  have h1 := GlobalTheory.VacCocycle.psi_half_symp_add B hB X W r s r' s' hX hW θ hθ v γ hγ γ' hγ'
  have h2 := GlobalTheory.VacCocycle.psi_half_symp_add B hB X W r s r' s' hX hW θ hθ v γ' hγ' γ hγ
  rw [add_comm γ' γ] at h2
  set S := symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) γ γ' with hS
  have hanti : symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) γ' γ = -S := by
    rw [hS, co.form, co.form]; ring
  rw [hanti] at h2
  have hne : ∀ x : AF F, B.ψ x ≠ 0 := fun x h => by
    have := AddChar.map_add_eq_mul B.ψ x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this
  set a := B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ)
  set b := B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ' γ')
  have hab : a * b ≠ 0 := mul_ne_zero (hne _) (hne _)
  have h3 : B.ψ (-(⅟(2 : AF F) * S)) = B.ψ (⅟(2 : AF F) * S) := by
    have := h1.symm.trans h2
    rw [mul_comm b a, mul_neg, neg_neg] at this
    exact mul_left_cancel₀ hab this
  have h4 : S = ⅟(2 : AF F) * S + -(-(⅟(2 : AF F) * S)) := by
    rw [neg_neg, ← two_mul, ← mul_assoc, mul_invOf_self, one_mul]
  rw [h4, AddChar.map_add_eq_mul, ← h3, ← AddChar.map_add_eq_mul, neg_neg, neg_add_cancel, AddChar.map_zero_eq_one]

end GlobalTheory.ThK.AdaptEv.VacuumBlock

namespace GlobalTheory.ThK.AdaptEv.VacuumBlock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem schr_indicator {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {ι : Type} [Fintype ι]
    (P : AddSubgroup (ι → R)) (a b : ι → R) (ha : a ∈ P) (hb : ∀ y ∈ P, ψ (y ⬝ᵥ b) = 1) :
    schr ψ (a, b) (Set.indicator (P : Set (ι → R)) 1) = ψ (⅟(2 : R) * (a ⬝ᵥ b)) • Set.indicator (P : Set (ι → R)) 1 := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ P
  · rw [Set.indicator_of_mem (show x + a ∈ (P : Set (ι → R)) from P.add_mem hx ha),
      Set.indicator_of_mem (show x ∈ (P : Set (ι → R)) from hx), AddChar.map_add_eq_mul, hb x hx]
    simp
  · have hxa : x + a ∉ (P : Set (ι → R)) := fun h => hx (by simpa using P.sub_mem h ha)
    rw [Set.indicator_of_notMem hxa, Set.indicator_of_notMem (show x ∉ (P : Set (ι → R)) from hx)]
    simp

theorem sum_of_inr {M κ ι κ₁ : Type} [AddCommMonoid M] [Fintype κ] [Fintype ι] [Fintype κ₁] (eq : κ ≃ ι ⊕ κ₁)
    (f : κ → M) (hf : ∀ j, f (eq.symm (Sum.inr j)) = 0) : ∑ k, f k = ∑ i, f (eq.symm (Sum.inl i)) := by
  rw [← eq.symm.sum_comp, Fintype.sum_sum_type]
  simp [hf]

theorem psi_eq_psiV (ψ : AddChar (AF F) ℂ) (v : Pl F) {z : AF F} (hz : At (evFin F v) z) :
    ψ z = GlobalTheory.VacAny.psiV ψ v (evFin F v z) := by
  rw [GlobalTheory.VacAny.psiV_apply, ← GlobalTheory.SchrLoc.eq_atPlace_of_at hz]

theorem finite_evaluation_extend_by_zero (v : Pl F) {κ ι κ₁ : Type} (eq : κ ≃ ι ⊕ κ₁) (a : κ₁ → AF F) (k : κ) :
    evFin F v (ext0 eq a k) = ext0 eq (fun j => evFin F v (a j)) k := by
  simp only [ext0]
  rcases eq k with i | j <;> simp

theorem prodVac_smul {κ ι κ₁ R : Type} (eq : κ ≃ ι ⊕ κ₁) (c₁ c₂ : ℂ) (A : (ι → R) → ℂ) (φ : (κ₁ → R) → ℂ) :
    prodVac eq (c₁ • A) (c₂ • φ) = (c₁ * c₂) • prodVac eq A φ := by
  funext x
  simp only [prodVac, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.ThK.AdaptEv.VacuumBlock

namespace GlobalTheory.ThK.AdaptEv.VacuumBlock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem phase {σ : E →ₐ[F] E} (B : Base F E) (hB : B.IsGood σ) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (M₁ : Model σ X₁ W₁)
    (r s r' s' i₀ i₁ j₀ j₁ : ℕ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
    {ι : Type} [Fintype ι] (eq : Fin n × Fin d ≃ ι ⊕ (Fin n₁ × Fin d₁))
    (hι : ∀ z, co.e (incM F H.ι * z * (incM F H'.ι)ᵀ) = (ext0 eq (M₁.co.e z).1, ext0 eq (M₁.co.e z).2))
    (θ : 𝓞 E) (hθ : (θ : E) + σ θ = 1) (v : Pl F) {p q g : Matrix _ _ _}
    (hpA : p ∈ spanA (F := F) H H') (hqA : q ∈ spanAd (F := F) H H')
    (hp : (co.e p).1 = 0 ∧ ∀ j, (co.e p).2 (eq.symm (Sum.inr j)) = 0)
    (hq : (co.e q).2 = 0 ∧ ∀ j, (co.e q).1 (eq.symm (Sum.inr j)) = 0)
    (hpΓ : p ∈ latAtV X W v) (hqΓ : q ∈ latAtV X W v) (hgΓ : incM F H.ι * g * (incM F H'.ι)ᵀ ∈ latAtV X W v) :
    B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J)
        (p + q + incM F H.ι * g * (incM F H'.ι)ᵀ) (p + q + incM F H.ι * g * (incM F H'.ι)ᵀ)) =
      B.ψ (⅟(2 : AF F) * ((co.e q).1 ⬝ᵥ (co.e p).2)) *
        B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X₁.J) (incM F W₁.J) g g) := by
  have hc := GlobalTheory.VacCocycle.psi_half_symp_add B hB X W r s r' s' hX hW θ hθ v
  rw [hc _ (add_mem hpΓ hqΓ) _ hgΓ, hc _ hpΓ _ hqΓ]
  obtain ⟨hiA, hiAd⟩ := GlobalTheory.ThK.AdaptEv.VacIso.spans_isotropic σ B X W X₁ W₁ H H' r' s' i₀ i₁ j₀ j₁
    (GlobalTheory.ThK.AdaptEv.VacIso.invol_of_isGood hB) hW hH hH'
  have e1 : symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) p p = 0 := by
    unfold symp; rw [hiA p hpA, mul_zero, map_zero]
  have e2 : symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) q q = 0 := by
    unfold symp; rw [hiAd q hqA, mul_zero, map_zero]
  have e3 : symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J)
      (incM F H.ι * g * (incM F H'.ι)ᵀ) (incM F H.ι * g * (incM F H'.ι)ᵀ) =
      symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X₁.J) (incM F W₁.J) g g := by
    unfold symp; rw [GlobalTheory.AdaptGram.hTens_adapted σ B X W X₁ W₁ H H' i₀ i₁ j₀ j₁ hH hH']
  have e4 : symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (p + q) (incM F H.ι * g * (incM F H'.ι)ᵀ) = 0 := by
    rw [co.form, hι, map_add, Prod.fst_add, Prod.snd_add, hp.1, hq.1, zero_add, add_zero]
    dsimp only
    rw [dotProduct_comm, ext0_dotProduct_of eq _ _ hq.2, ext0_dotProduct_of eq _ _ hp.2, sub_zero]
  have e5 : symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) p q = -((co.e q).1 ⬝ᵥ (co.e p).2) := by
    rw [co.form, hp.1, zero_dotProduct, zero_sub]
  rw [e1, e2, e3, e4, e5]
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_neg, neg_neg, one_mul, mul_one]

end GlobalTheory.ThK.AdaptEv.VacuumBlock

namespace GlobalTheory.ThK.AdaptEv.VacuumBlock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem local_vac {σ : E →ₐ[F] E} (B : Base F E) {n d n₁ d₁ : ℕ} (r s r' s' i₀ i₁ j₀ j₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (M₁ : Model σ X₁ W₁)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
    {ι : Type} [Fintype ι] (eq : Fin n × Fin d ≃ ι ⊕ (Fin n₁ × Fin d₁)) (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hM₁ : M₁.IsGood B.ψ)
    (hrat : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (hι : ∀ z, co.e (incM F H.ι * z * (incM F H'.ι)ᵀ) = (ext0 eq (M₁.co.e z).1, ext0 eq (M₁.co.e z).2))
    (hA : ∀ u ∈ isoA H H', (co.e u).1 = 0 ∧ ∀ j, (co.e u).2 (eq.symm (Sum.inr j)) = 0)
    (hAd : ∀ u ∈ isoAd H H', (co.e u).2 = 0 ∧ ∀ j, (co.e u).1 (eq.symm (Sum.inr j)) = 0) (v : Pl F) :
    Model.IsVac (Model.mk (σ := σ) (X := X) (W := W) co (fun _ => 0) 0 ∅) B.ψ v
      (prodVac eq (Set.indicator (latPos X W co eq v : Set (ι → Fv F v)) 1) (M₁.vac v)) := by
  set P := latPos X W co eq v with hPdef
  obtain ⟨hφSB, hφ0, θ, hθ, hφact⟩ := hM₁.vac v
  have hASB := GlobalTheory.ThK.AdaptEv.VacuumBlock.latPos_indicator_mem_SB σ B X W r s r' s' co eq hX hW hrat v
  refine ⟨(sb_restrL_prodVac eq).2 _ hASB _ hφSB, fun h0 => hφ0 ?_, θ, hθ, ?_⟩
  · funext y
    have := congrFun h0 (ext0 eq y)
    rw [prodVac_ext0, Set.indicator_of_mem (show (0 : ι → Fv F v) ∈ (P : Set (ι → Fv F v)) from P.zero_mem),
      Pi.one_apply, one_mul] at this
    exact this
  intro γ hγ
  obtain ⟨p, hpA, q, hqA, g, hg, hpΓ, hqΓ, rfl⟩ := GlobalTheory.ThK.AdaptEv.VacuumBlock.latAtV_adapted_decomp σ B X W X₁ W₁ H H' i₀ i₁ j₀ j₁ hH hH' v γ hγ
  have hgΓ : incM F H.ι * g * (incM F H'.ι)ᵀ ∈ latAtV X W v := by
    have e : incM F H.ι * g * (incM F H'.ι)ᵀ = (p + q + incM F H.ι * g * (incM F H'.ι)ᵀ) - p - q := by abel
    rw [e]; exact sub_mem (sub_mem hγ hpΓ) hqΓ
  have hp : (co.e p).1 = 0 ∧ ∀ j, (co.e p).2 (eq.symm (Sum.inr j)) = 0 := by
    obtain ⟨y, z, rfl⟩ := hpA
    have h1 := hA _ (Or.inl ⟨y, rfl⟩)
    have h2 := hA _ (Or.inr ⟨z, rfl⟩)
    rw [map_add]
    exact ⟨by rw [Prod.fst_add, h1.1, h2.1, add_zero], fun j => by rw [Prod.snd_add, Pi.add_apply, h1.2, h2.2, add_zero]⟩
  have hq : (co.e q).2 = 0 ∧ ∀ j, (co.e q).1 (eq.symm (Sum.inr j)) = 0 := by
    obtain ⟨y, z, rfl⟩ := hqA
    have h1 := hAd _ (Or.inl ⟨y, rfl⟩)
    have h2 := hAd _ (Or.inr ⟨z, rfl⟩)
    rw [map_add]
    exact ⟨by rw [Prod.snd_add, h1.1, h2.1, add_zero], fun j => by rw [Prod.fst_add, Pi.add_apply, h1.2, h2.2, add_zero]⟩
  have hAtγ := at_of_mem co v _ hγ
  have hAtp := at_of_mem co v _ hpΓ
  have hAtq := at_of_mem co v _ hqΓ
  have hAtg := at_of_mem M₁.co v _ hg

  set α : Fin n × Fin d → Fv F v := fun k => evFin F v ((co.e q).1 k) with hα
  set β : Fin n × Fin d → Fv F v := fun k => evFin F v ((co.e p).2 k) with hβ
  set a : Fin n₁ × Fin d₁ → Fv F v := fun j => evFin F v ((M₁.co.e g).1 j) with ha
  set b : Fin n₁ × Fin d₁ → Fv F v := fun j => evFin F v ((M₁.co.e g).2 j) with hb
  have hαr : ∀ j, α (eq.symm (Sum.inr j)) = 0 := fun j => by simp only [hα, hq.2 j, map_zero]
  have hβr : ∀ j, β (eq.symm (Sum.inr j)) = 0 := fun j => by simp only [hβ, hp.2 j, map_zero]
  have hw : ((fun i => evFin F v ((co.e (p + q + incM F H.ι * g * (incM F H'.ι)ᵀ)).1 i)),
      (fun i => evFin F v ((co.e (p + q + incM F H.ι * g * (incM F H'.ι)ᵀ)).2 i))) = (α + ext0 eq a, β + ext0 eq b) := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · simp only [map_add, hι, Prod.fst_add, Pi.add_apply, hp.1, Pi.zero_apply, zero_add, finite_evaluation_extend_by_zero, hα, ha]
    · simp only [map_add, hι, Prod.snd_add, Pi.add_apply, hq.1, Pi.zero_apply, add_zero, finite_evaluation_extend_by_zero, hβ, hb]

  have hαP : (fun i => α (eq.symm (Sum.inl i))) ∈ P := mem_latPos.2 ⟨q, hqΓ, fun i => rfl⟩
  have hβP : ∀ y ∈ P, GlobalTheory.VacAny.psiV B.ψ v (y ⬝ᵥ fun i => β (eq.symm (Sum.inl i))) = 1 := by
    intro y hy
    obtain ⟨γ', hγ', hy⟩ := mem_latPos.1 hy
    have hAt' := at_of_mem co v _ hγ'
    have e1 : y ⬝ᵥ (fun i => β (eq.symm (Sum.inl i))) = evFin F v ((co.e γ').1 ⬝ᵥ (co.e p).2) := by
      simp only [dotProduct, map_sum, map_mul, hβ, ← hy]
      rw [sum_of_inr eq _ (fun j => by rw [hp.2 j, map_zero, mul_zero])]
    have hz : At (evFin F v) ((co.e γ').1 ⬝ᵥ (co.e p).2) :=
      GlobalTheory.VacAny.at_sum _ fun k _ => GlobalTheory.VacAny.at_mul_right (hAt' k).1 _
    rw [e1, ← psi_eq_psiV B.ψ v hz]
    have e2 : (co.e γ').1 ⬝ᵥ (co.e p).2 = symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) γ' p := by
      rw [co.form, hp.1, zero_dotProduct, sub_zero]
    rw [e2]
    exact psi_symp_eq_one B hB X W r s r' s' hX hW co v γ' hγ' p hpΓ

  have hφ1 : schr (GlobalTheory.VacAny.psiV B.ψ v) (a, b) (M₁.vac v) =
      B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X₁.J) (incM F W₁.J) g g) •
        M₁.vac v :=
    GlobalTheory.AdelicActs.schr_local_of_acts B.ψ v (M₁.co.e g) (fun i => (hAtg i).1) (fun i => (hAtg i).2) _ _ hφSB (hφact g hg)

  have hph := phase B hB X W X₁ W₁ H H' M₁ r s r' s' i₀ i₁ j₀ j₁ hX hW hH hH' co eq hι θ hθ v hpA hqA hp hq hpΓ hqΓ hgΓ
  have hD : B.ψ (⅟(2 : AF F) * ((co.e q).1 ⬝ᵥ (co.e p).2)) =
      GlobalTheory.VacAny.psiV B.ψ v (⅟(2 : Fv F v) * ((fun i => α (eq.symm (Sum.inl i))) ⬝ᵥ fun i => β (eq.symm (Sum.inl i)))) := by
    have hz : At (evFin F v) (⅟(2 : AF F) * ((co.e q).1 ⬝ᵥ (co.e p).2)) :=
      GlobalTheory.VacAny.at_mul_left _ (GlobalTheory.VacAny.at_sum _ fun k _ => GlobalTheory.VacAny.at_mul_right (hAtq k).1 _)
    rw [psi_eq_psiV B.ψ v hz, map_mul, GlobalTheory.VacAny.evFin_invOf_two]
    congr 2
    simp only [dotProduct, map_sum, map_mul, hα, hβ]
    rw [sum_of_inr eq _ (fun j => by rw [hp.2 j, map_zero, mul_zero])]
  intro rr hrr
  show schr B.ψ (co.e (p + q + incM F H.ι * g * (incM F H'.ι)ᵀ)) _ = _
  rw [GlobalTheory.SchrLoc.schr_tens_of_at B.ψ v _ (fun i => (hAtγ i).1) (fun i => (hAtγ i).2) _ rr hrr.1]
  congr 1
  rw [hw, GlobalTheory.ThK.AdaptEv.schroedinger_ext_zero_product_vacuum _ eq α β a b _ _ hαr hβr, schr_indicator _ P _ _ hαP hβP, hφ1, prodVac_smul, hph, hD]

end GlobalTheory.ThK.AdaptEv.VacuumBlock

theorem GlobalTheory.ThK.AdaptEv.exists_vac_adapted_isoA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (M₁ : Model σ X₁ W₁)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
    (eq : Fin n × Fin d ≃ Fin (2 * (n + d₁)) ⊕ (Fin n₁ × Fin d₁)), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ z, co.e (incM F H.ι * z * (incM F H'.ι)ᵀ) = (ext0 eq (M₁.co.e z).1, ext0 eq (M₁.co.e z).2)) →
    (∀ u ∈ isoA H H', (co.e u).1 = 0 ∧ ∀ j, (co.e u).2 (eq.symm (Sum.inr j)) = 0) →
    (∀ u ∈ isoAd H H', (co.e u).2 = 0 ∧ ∀ j, (co.e u).1 (eq.symm (Sum.inr j)) = 0) →
    ∃ A : ∀ v : Pl F, (Fin (2 * (n + d₁)) → Fv F v) → ℂ,
      (∀ v, A v ∈ SB _ ∧ A v 0 = 1 ∧
        Model.IsVac (Model.mk (σ := σ) (X := X) (W := W) co (fun _ => 0) 0 ∅) B.ψ v (prodVac eq (A v) (M₁.vac v))) ∧
      ∀ᶠ v in cofinite, A v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M₁ co eq hB hX hW hH hH' hM₁ hrat hι hA hAd
  classical
  let good : Pl F → Prop := fun v =>
    M₁.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      (Model.mk (σ := σ) (X := X) (W := W) co (fun _ => 0) 0 ∅).IsVac B.ψ v
        (Set.indicator {x : Fin n × Fin d → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1)
  refine ⟨fun v => if good v then Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
    else Set.indicator (GlobalTheory.ThK.AdaptEv.VacuumBlock.latPos X W co eq v : Set (Fin (2 * (n + d₁)) → Fv F v)) 1,
    fun v => ?_, ?_⟩
  · by_cases hv : good v
    · simp only [if_pos hv]
      refine ⟨GlobalTheory.StdVacuum.indicator_mem_SB v, ?_, ?_⟩
      · rw [Set.indicator_of_mem (show (0 : Fin (2 * (n + d₁)) → Fv F v) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from
          fun i => zero_mem _)]
        rfl
      · rw [hv.1]
        convert hv.2 using 1
        exact prodVac_indicator eq (v.adicCompletionIntegers F : Set (Fv F v))
    · simp only [if_neg hv]
      refine ⟨GlobalTheory.ThK.AdaptEv.VacuumBlock.latPos_indicator_mem_SB σ B X W r s r' s' co eq hX hW hrat v, ?_,
        GlobalTheory.ThK.AdaptEv.VacuumBlock.local_vac B r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M₁ co eq hB hX hW hH hH' hM₁ hrat hι hA hAd v⟩
      rw [Set.indicator_of_mem (show (0 : Fin (2 * (n + d₁)) → Fv F v) ∈
        ((GlobalTheory.ThK.AdaptEv.VacuumBlock.latPos X W co eq v : AddSubgroup _) : Set (Fin (2 * (n + d₁)) → Fv F v)) from
          (GlobalTheory.ThK.AdaptEv.VacuumBlock.latPos X W co eq v).zero_mem)]
      rfl
  · filter_upwards [hM₁.std, GlobalTheory.StdVacuum.eventually_isVac_indicator σ B X W r s r' s' hB hX hW
      (Model.mk (σ := σ) (X := X) (W := W) co (fun _ => 0) 0 ∅) hrat] with v h1 h2
    simp only [if_pos (show good v from ⟨h1, h2⟩)]
