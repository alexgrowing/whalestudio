import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankEqFinrankEigenInter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichKernelRangeExact
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.DetInv.PadicInclusionHoms

section Homs

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ]

noncomputable abbrev padicIncl (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] : Λ →+* ℤ_[p] ⊗[ℤ] Λ :=
  (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[p] ⊗[ℤ] Λ).toRingHom

omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem tmul_eq_algebraMap_mul (r : ℤ_[p]) (a : Λ) :
    (r ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] Λ) = algebraMap ℤ_[p] (ℤ_[p] ⊗[ℤ] Λ) r * padicIncl p Λ a := by
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]

theorem hom_algebraMap_padic {Γ : Type} [CommRing Γ] [Algebra ℤ_[p] Γ] (σ : Γ →+* O) (r : ℤ_[p]) :
    σ (algebraMap ℤ_[p] Γ r) = padicToO p O r :=
  RingHom.congr_fun (GlobalTheory.padicToO_unique p O (σ.comp (algebraMap ℤ_[p] Γ))) r

theorem hom_ext_padicIncl {σ σ' : ℤ_[p] ⊗[ℤ] Λ →+* O}
    (h : σ.comp (padicIncl p Λ) = σ'.comp (padicIncl p Λ)) : σ = σ' := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r a =>
    rw [tmul_eq_algebraMap_mul, map_mul, map_mul, hom_algebraMap_padic, hom_algebraMap_padic]
    exact congrArg _ (RingHom.congr_fun h a)

theorem exists_hom_padicIncl (τ : Λ →+* O) :
    ∃ σ : ℤ_[p] ⊗[ℤ] Λ →+* O, σ.comp (padicIncl p Λ) = τ :=
  ⟨(Algebra.TensorProduct.lift (padicToO p O).toIntAlgHom τ.toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom, RingHom.ext fun a => by simp⟩

theorem mem_eig_iff {C : Type} [Field C] [Algebra O C] {h : ℕ} {Γ : Type} [CommRing Γ]
    (ρ : Γ → Matrix (Fin h) (Fin h) O) (σ : Γ →+* O) (x : Fin h → C) :
    x ∈ eig C ρ σ ↔ ∀ a, (ρ a).map (algebraMap O C) *ᵥ x = algebraMap O C (σ a) • x := by
  simp [eig, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

theorem mem_eig_iff_padicIncl {C : Type} [Field C] [Algebra O C] {h : ℕ}
    (ρ : ℤ_[p] ⊗[ℤ] Λ →+* Matrix (Fin h) (Fin h) O)
    (hρ : ∀ r, ρ (algebraMap ℤ_[p] _ r) = padicToO p O r • (1 : Matrix (Fin h) (Fin h) O))
    (σ : ℤ_[p] ⊗[ℤ] Λ →+* O) (x : Fin h → C) :
    x ∈ eig C ρ σ ↔ ∀ a, (ρ (padicIncl p Λ a)).map (algebraMap O C) *ᵥ x =
      algebraMap O C (σ (padicIncl p Λ a)) • x := by
  rw [mem_eig_iff]
  refine ⟨fun H a => H _, fun H g => ?_⟩
  induction g using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, Matrix.map_add _ (map_add _), Matrix.add_mulVec, hx, hy, map_add, map_add, add_smul]
  | tmul r a =>
    have e : (padicToO p O r • ρ (padicIncl p Λ a)).map (algebraMap O C) =
        algebraMap O C (padicToO p O r) • (ρ (padicIncl p Λ a)).map (algebraMap O C) := by
      ext i j; simp
    rw [tmul_eq_algebraMap_mul, map_mul, map_mul, hρ, hom_algebraMap_padic, smul_mul_assoc, one_mul,
      e, Matrix.smul_mulVec, H, smul_smul, map_mul]

theorem iSup_eig_eq_top_of_isSplitting {C : Type} [Field C] [Algebra O C] {h : ℕ}
    (ρ : ℤ_[p] ⊗[ℤ] Λ →+* Matrix (Fin h) (Fin h) O)
    (hρ : ∀ r, ρ (algebraMap ℤ_[p] _ r) = padicToO p O r • (1 : Matrix (Fin h) (Fin h) O))
    {J : Type} [Finite J] {τ : J → Λ →+* O} (hτ : EigenSplit.IsSplitting (embC C τ)) :
    (⨆ σ : ℤ_[p] ⊗[ℤ] Λ →+* O, eig C ρ σ) = ⊤ := by
  classical
  have := Fintype.ofFinite J
  let ρ' : Λ →+* Module.End C (Fin h → C) :=
    (Matrix.toLinAlgEquiv' (R := C) (n := Fin h)).toRingEquiv.toRingHom.comp
      ((algebraMap O C).mapMatrix.comp (ρ.comp (padicIncl p Λ)))
  rw [eq_top_iff]
  intro x _
  rw [← EigenSplit.sum_proj hτ ρ' x]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨σ, hσ⟩ := exists_hom_padicIncl (p := p) (τ i)
  refine Submodule.mem_iSup_of_mem σ ((mem_eig_iff_padicIncl ρ hρ σ _).2 fun a => ?_)
  have h1 := EigenSplit.mem_eigenSub.1 (EigenSplit.proj_mem hτ ρ' i x) a
  have h2 : σ (padicIncl p Λ a) = τ i a := RingHom.congr_fun hσ a
  rw [h2]
  exact h1

end Homs

theorem exists_eq_embO {C : Type} [Field C] [CharZero C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {E : Type} [Field E] [NumberField E]
    (τ : 𝓞 E →+* O) : ∃ ψ : E →+* C, τ = embO hv ψ := by
  have hinj : Function.Injective ((algebraMap O C).comp τ) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  refine ⟨IsFractionRing.lift hinj, RingHom.ext fun a => hv.hom_inj ?_⟩
  rw [algebraMap_embO]
  exact (IsFractionRing.lift_algebraMap hinj a).symm

section Comparison₂

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C]
  [IsScalarTower ℤ_[p] O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P : Point p v O Λ}
  {ε : PreTilt O p} {h : ℕ} {D : Datum ε h (ℤ_[p] ⊗[ℤ] Λ)} {φ : P.V ≃ₗ[C] (Fin h → C)}

omit [IsAlgClosed C] [CharZero C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  [StarRing Λ] in
theorem actT_algebraMap (D : Datum ε h (ℤ_[p] ⊗[ℤ] Λ)) (r : ℤ_[p]) :
    ((padicToO p O).mapMatrix.comp D.ρT.toRingHom) (algebraMap ℤ_[p] _ r) =
      padicToO p O r • (1 : Matrix (Fin h) (Fin h) O) := by
  have e : D.ρT (algebraMap ℤ_[p] _ r) = algebraMap ℤ_[p] _ r := D.ρT.commutes r
  change (D.ρT (algebraMap ℤ_[p] _ r)).map (padicToO p O) = _
  rw [e]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply, hij]

theorem mem_wRec_iff (hb : Function.Injective P.bLie) (τ : Λ →+* O) (x : P.V) :
    x ∈ P.wRec τ ↔ x ∈ P.latLie ∧ x ∈ P.eigV τ := by
  refine ⟨fun hx => P.wRec_le τ hx, ?_⟩
  rintro ⟨⟨y, rfl⟩, hy⟩
  refine ⟨⟨y, fun a => hb ?_⟩, rfl⟩
  rw [P.bLie_act, P.bLie_scale, EigenSplit.mem_eigenSub.1 hy a, RingHom.comp_apply, algebraMap_smul]

theorem mem_eigV_iff (ht : IsTie P D (padicIncl p Λ) φ) (σ : ℤ_[p] ⊗[ℤ] Λ →+* O) (x : P.V) :
    x ∈ P.eigV (σ.comp (padicIncl p Λ)) ↔ φ x ∈ eig C (actT D) σ := by
  have e := mem_eig_iff_padicIncl ((padicToO p O).mapMatrix.comp D.ρT.toRingHom)
    (actT_algebraMap D) σ (φ x)
  refine EigenSplit.mem_eigenSub.trans (Iff.trans (forall_congr' fun a => ?_) e.symm)
  rw [← φ.injective.eq_iff, ht.act, map_smul]
  rfl

omit [IsAlgClosed C] [CharZero C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  [StarRing Λ] in
theorem mem_lieSub_iff (hv : v.Integers O) (D : Datum ε h (ℤ_[p] ⊗[ℤ] Λ))
    (σ : ℤ_[p] ⊗[ℤ] Λ →+* O) (z : Fin h → C) :
    z ∈ lieSub C D σ ↔ z ∈ D.Lie.map (incl C h) ∧ z ∈ eig C (actT D) σ := by
  have key : ∀ y : Fin h → O, y ∈ D.Tsub σ ↔ incl C h y ∈ eig C (actT D) σ := by
    intro y
    rw [mem_eig_iff, Datum.Tsub, Submodule.mem_iInf]
    refine forall_congr' fun a => ?_
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, funext_iff, funext_iff]
    refine forall_congr' fun i => ?_
    rw [← hv.hom_inj.eq_iff, RingHom.map_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rfl
  constructor
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨y, h1, rfl⟩, (key y).1 h2⟩
  · rintro ⟨⟨y, h1, rfl⟩, h2⟩
    exact ⟨y, ⟨h1, (key y).2 h2⟩, rfl⟩

theorem mem_latT_iff_incl (ht : IsTie P D (padicIncl p Λ) φ) (x : P.V) :
    x ∈ P.latT ↔ φ x ∈ (⊤ : Submodule O (Fin h → O)).map (incl C h) := by
  rw [ht.lat]
  constructor
  · intro H
    choose y hy using H
    exact ⟨y, trivial, funext hy⟩
  · rintro ⟨y, -, hy⟩ i
    exact ⟨y i, congrFun hy i⟩

theorem map_latTQuot (ht : IsTie P D (padicIncl p Λ) φ) {J : Type} [DecidableEq J] [Finite J]
    {τ : J → Λ →+* O} (hτ : EigenSplit.IsSplitting (embC C τ)) (hall : ∀ t : Λ →+* O, ∃ i, t = τ i)
    (σ : ℤ_[p] ⊗[ℤ] Λ →+* O) (i : J) (hσ : σ.comp (padicIncl p Λ) = τ i) :
    (P.latTQuot hτ i).map ((φ : P.V →ₗ[C] (Fin h → C)).restrictScalars O) =
      eigPart C (actT D) σ ⊤ := by
  have := Fintype.ofFinite J
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨t, htl, rfl⟩, rfl⟩
    change φ (EigenSplit.proj hτ P.actV i t) ∈ _
    refine ⟨(mem_eigV_iff ht σ _).1 (hσ ▸ EigenSplit.proj_mem hτ P.actV i t), ?_⟩
    have e : φ (EigenSplit.proj hτ P.actV i t) =
        φ t - ∑ k ∈ Finset.univ.erase i, φ (EigenSplit.proj hτ P.actV k t) := by
      rw [eq_sub_iff_add_eq, ← map_sum, ← map_add,
        Finset.add_sum_erase _ (fun k => EigenSplit.proj hτ P.actV k t) (Finset.mem_univ i),
        EigenSplit.sum_proj]
    rw [e]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left ((mem_latT_iff_incl ht t).1 htl))
      (Submodule.mem_sup_right ?_)
    rw [Submodule.restrictScalars_mem]
    refine Submodule.sum_mem _ fun k hk => ?_
    obtain ⟨σ', hσ'⟩ := exists_hom_padicIncl (p := p) (τ k)
    have hne : σ' ≠ σ := by
      rintro rfl
      exact Finset.ne_of_mem_erase hk (hτ.injective (congrArg (algebraMap O C).comp (hσ'.symm.trans hσ)))
    exact Submodule.mem_iSup_of_mem (⟨σ', hne⟩ : {s // s ≠ σ})
      ((mem_eigV_iff ht σ' _).1 (hσ' ▸ EigenSplit.proj_mem hτ P.actV k t))
  · rintro y ⟨hy1, hy2⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy2
    obtain ⟨a, rfl⟩ := φ.surjective a
    obtain ⟨b, rfl⟩ := φ.surjective b
    have h1 : a + b ∈ P.eigV (τ i) := hσ ▸ (mem_eigV_iff ht σ _).2 (by rw [map_add]; exact hy1)
    have h2 : (⨆ s : {s : ℤ_[p] ⊗[ℤ] Λ →+* O // s ≠ σ}, eig C (actT D) s.1) ≤
        LinearMap.ker (EigenSplit.proj hτ P.actV i ∘ₗ φ.symm.toLinearMap) := by
      refine iSup_le fun s z hz => ?_
      obtain ⟨z, rfl⟩ := φ.surjective z
      obtain ⟨k, hk⟩ := hall (s.1.comp (padicIncl p Λ))
      have hne : k ≠ i := by
        rintro rfl
        exact s.2 (hom_ext_padicIncl (hk.trans hσ.symm))
      have h3 : z ∈ P.eigV (τ k) := hk ▸ (mem_eigV_iff ht s.1 _).2 hz
      simpa using EigenSplit.proj_of_mem_ne hτ hne h3
    have h3 : EigenSplit.proj hτ P.actV i b = 0 := by simpa using h2 hb
    refine ⟨a + b, ⟨a, (mem_latT_iff_incl ht a).2 ha, ?_⟩, map_add φ a b⟩
    change EigenSplit.proj hτ P.actV i a = _
    rw [← EigenSplit.proj_of_mem hτ h1, map_add, h3, add_zero]

end Comparison₂

theorem eig_lattices_of_isTie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (ε : PreTilt O p) (h : ℕ) (D : Datum ε h (ℤ_[p] ⊗[ℤ] 𝓞 E)) (φ : P.V ≃ₗ[C] (Fin h → C)), IsPrimitiveRoot (root ε).untilt p → IsTie P D (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom φ → (⨆ σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O, eig C (actT D) σ) = ⊤ ∧ (⨆ σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O, eig C (actH D) σ) = ⊤ ∧ (∀ σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O, ∃ ψ : E →+* C, σ.comp (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom = embO P.integers ψ) ∧ ∀ (σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O) (ψ : E →+* C), σ.comp (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom = embO P.integers ψ → (P.eigV (embO P.integers ψ)).map (φ : P.V →ₗ[C] (Fin h → C)) = eig C (actT D) σ ∧ (P.wRec (embO P.integers ψ)).map ((φ : P.V →ₗ[C] (Fin h → C)).restrictScalars O) = lieSub C D σ ∧ (open Classical in P.latTQuot (σ := fun φ' : E →+* C => embO P.integers φ') (isSplitting_embO P.integers) ψ).map ((φ : P.V →ₗ[C] (Fin h → C)).restrictScalars O) = eigPart C (actT D) σ ⊤ ∧ D.lieRank σ = Module.finrank C (P.eigW (embO P.integers ψ)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ E _ _ _ P ε h D φ hε ht
  have hv := P.integers
  refine ⟨?_, ?_, fun σ => exists_eq_embO hv _, fun σ ψ hσ => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact iSup_eig_eq_top_of_isSplitting ((padicToO p O).mapMatrix.comp D.ρT.toRingHom)
      (actT_algebraMap D) (isSplitting_embO hv)
  · refine iSup_eig_eq_top_of_isSplitting ((WittVector.fontaineTheta O p).mapMatrix.comp D.ρM)
      (fun r => ?_) (isSplitting_embO hv)
    change (D.ρM (algebraMap ℤ_[p] _ r)).map (WittVector.fontaineTheta O p) = _
    rw [(datum_scalar_intertwine p C v O hv ε hε _ h D).1]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, padicToO, hij]
  · rw [← hσ]
    ext z
    obtain ⟨z, rfl⟩ := φ.surjective z
    rw [← mem_eigV_iff ht]
    exact ⟨fun ⟨y, hy, e⟩ => φ.injective e ▸ hy, fun hz => ⟨z, hz, rfl⟩⟩
  · rw [← hσ]
    ext z
    obtain ⟨z, rfl⟩ := φ.surjective z
    rw [mem_lieSub_iff hv, ← mem_eigV_iff ht, ← ht.lie, ← mem_wRec_iff ht.lieInj]
    exact ⟨fun ⟨y, hy, e⟩ => φ.injective e ▸ hy, fun hz => ⟨z, hz, rfl⟩⟩
  · classical
    exact map_latTQuot ht _ (exists_eq_embO hv) σ ψ hσ
  · rw [lieRank_eq_finrank_range_bC_inf_eig p C v O hv ε _ h D σ,
      ← (ker_bC_eq_range_alC_and_ker_alC_eq_range_bC p C v O hv ε hε _ h D).2, ← hσ,
      ← LinearEquiv.finrank_map_eq φ]
    refine congrArg (fun S : Submodule C (Fin h → C) => Module.finrank C S) ?_
    ext z
    obtain ⟨z, rfl⟩ := φ.surjective z
    rw [Submodule.mem_inf, ← mem_eigV_iff ht, LinearMap.mem_ker, ← ht.ker]
    exact ⟨fun hz => ⟨z, hz, rfl⟩, fun ⟨y, hy, e⟩ => φ.injective e ▸ hy⟩

end GlobalTheory.DetInv.PadicInclusionHoms
