import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroTraceElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomIntegersInjectiveOfCharZero
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

namespace UpperTheory.CutDual

private theorem span_of_casimir {O La V K : Type} [CommRing O] [AddCommGroup La] [Module O La] [CommRing V] [Field K]
    (β : V →+* K) (σ : O →+* V) {M N : ℕ} (a : Fin M → La) (T : Fin N → Fin M → V)
    (hL : ∀ x : V ⊗[ℤ] La, (∀ o, ((LinearMap.lsmul O La o).restrictScalars ℤ).baseChange V x = σ o • x) →
      x ∈ Submodule.span V (Set.range fun i => ∑ m, T i m ⊗ₜ[ℤ] a m))
    {d : ℕ} (c θ : Fin d → O) (hc : ∀ o : O, ∑ j, c j ⊗ₜ[ℤ] (o * θ j) = ∑ j, (o * c j) ⊗ₜ[ℤ] θ j)
    (hne : β (σ (∑ j, c j * θ j)) ≠ 0) (w : K ⊗[ℤ] La)
    (hw : ∀ o, ((LinearMap.lsmul O La o).restrictScalars ℤ).baseChange K w = β (σ o) • w) :
    w ∈ Submodule.span K (Set.range fun i => ∑ m, β (T i m) ⊗ₜ[ℤ] a m) := by
  set Sp := Submodule.span K (Set.range fun i => ∑ m, β (T i m) ⊗ₜ[ℤ] a m) with hSp
  let Q : K ⊗[ℤ] La →ₗ[K] K ⊗[ℤ] La :=
    ∑ j, β (σ (c j)) • ((LinearMap.lsmul O La (θ j)).restrictScalars ℤ).baseChange K
  let phi : V ⊗[ℤ] La →ₗ[ℤ] K ⊗[ℤ] La := TensorProduct.map β.toIntAlgHom.toLinearMap LinearMap.id
  have phi_tmul : ∀ v b, phi (v ⊗ₜ b) = β v ⊗ₜ b := fun v b => TensorProduct.map_tmul _ _ v b
  have phi_smul : ∀ v y, phi (v • y) = β v • phi y := by
    intro v y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v' b =>
      rw [TensorProduct.smul_tmul', phi_tmul, phi_tmul, TensorProduct.smul_tmul']
      simp
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  have hΦ : ∀ y ∈ Submodule.span V (Set.range fun i => ∑ m, T i m ⊗ₜ[ℤ] a m), phi y ∈ Sp := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [map_sum]
      simp only [phi_tmul]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Sp.add_mem hx hy
    | smul v x _ hx => rw [phi_smul]; exact Sp.smul_mem _ hx
  have hb : ∀ b : La, Q (1 ⊗ₜ b) ∈ Sp := by
    intro b
    let g : O →ₗ[ℤ] La := (LinearMap.toSpanSingleton O La b).restrictScalars ℤ
    have hx : (∑ j, σ (c j) ⊗ₜ[ℤ] (θ j • b)) ∈
        Submodule.span V (Set.range fun i => ∑ m, T i m ⊗ₜ[ℤ] a m) := by
      apply hL
      intro o
      have h1 := congrArg (TensorProduct.map σ.toIntAlgHom.toLinearMap g) (hc o)
      simp only [map_sum, TensorProduct.map_tmul] at h1
      simp only [map_sum, LinearMap.baseChange_tmul, Finset.smul_sum, TensorProduct.smul_tmul']
      simp only [g, LinearMap.restrictScalars_apply, LinearMap.toSpanSingleton_apply, mul_smul, map_mul,
        AlgHom.toLinearMap_apply] at h1
      exact h1
    have h2 := hΦ _ hx
    convert h2 using 1
    simp [Q, LinearMap.sum_apply, LinearMap.baseChange_tmul, TensorProduct.smul_tmul', phi_tmul]
  have hall : ∀ w, Q w ∈ Sp := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul z t =>
      have he : z ⊗ₜ[ℤ] t = z • ((1 : K) ⊗ₜ[ℤ] t) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [he, map_smul]
      exact Sp.smul_mem _ (hb t)
    | add x y hx hy => rw [map_add]; exact Sp.add_mem hx hy
  have hQ : Q w = β (σ (∑ j, c j * θ j)) • w := by
    simp only [Q, LinearMap.sum_apply, LinearMap.smul_apply, hw, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    simp [map_sum, map_mul]
  have : w = (β (σ (∑ j, c j * θ j)))⁻¹ • Q w := by
    rw [hQ, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [this]
  exact Sp.smul_mem _ (hall w)

private theorem coeff_eq {La K : Type} [AddCommGroup La] [CommRing K] (B : LinearMap.BilinForm ℤ La)
    (halt : ∀ x y, B x y = -B y x) {M N : ℕ} (a : Fin M → La) (T S : Fin N → Fin M → K)
    (hd : ∀ i j, ∑ m, ∑ m', S i m * T j m' * ((B (a m) (a m') : ℤ) : K) = if i = j then 1 else 0)
    (c : Fin N → K) (i : Fin N) :
    ∑ m, S i m * B.baseChange K (∑ j, c j • ∑ m', T j m' ⊗ₜ[ℤ] a m') (1 ⊗ₜ a m) = -c i := by
  have h1 : ∀ m, S i m * B.baseChange K (∑ j, c j • ∑ m', T j m' ⊗ₜ[ℤ] a m') (1 ⊗ₜ a m) =
      -∑ j, c j * ∑ m', S i m * T j m' * ((B (a m) (a m') : ℤ) : K) := by
    intro m
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.BilinForm.baseChange_tmul,
      smul_eq_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m' _ => ?_
    rw [halt (a m') (a m)]
    simp only [zsmul_eq_mul, Int.cast_neg]
    ring
  simp only [h1]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  simp only [← Finset.mul_sum, hd]
  simp

private theorem pair_eq {La K : Type} [AddCommGroup La] [CommRing K] (B : LinearMap.BilinForm ℤ La)
    {M N : ℕ} (a : Fin M → La) (T : Fin N → Fin M → K) (c : Fin N → K) (y : K ⊗[ℤ] La) :
    ∑ j, (∑ m, T j m * B.baseChange K y (1 ⊗ₜ a m)) * (-c j) =
      -B.baseChange K y (∑ j, c j • ∑ m', T j m' ⊗ₜ[ℤ] a m') := by
  rw [map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_sum, smul_eq_mul, mul_neg, mul_comm]
  congr 2
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]

private theorem norm_pair_le {La K : Type} [AddCommGroup La] [NormedField K] [IsUltrametricDist K]
    (B : LinearMap.BilinForm ℤ La)
    {M N : ℕ} (a : Fin M → La) (T : Fin N → Fin M → K) (hT : ∀ j m, ‖T j m‖ ≤ 1) (c : Fin N → K)
    (hc : ∀ j, ‖c j‖ ≤ 1) (b : La) :
    ‖B.baseChange K (∑ j, c j • ∑ m', T j m' ⊗ₜ[ℤ] a m') (1 ⊗ₜ b)‖ ≤ 1 := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.BilinForm.baseChange_tmul,
      smul_eq_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
  rw [norm_mul]
  refine mul_le_one₀ (hc j) (norm_nonneg _) ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun m _ => ?_
  rw [zsmul_eq_mul, _root_.mul_one, norm_mul]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one K _) (norm_nonneg _) (hT j m)

end UpperTheory.CutDual

theorem UpperTheory.lattice_data_gives_cut_and_dual :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (s : 𝓞 E →+* ↥(intO ℂ_[p])) (M N : ℕ) (a : Fin M → Dw.La) (T S : Fin N → Fin M → ↥(intO ℂ_[p])), GlobalTheory.FlatModel.LatData Dw s a T S → CutL Dw ((intO ℂ_[p]).subtype.comp s) a (fun j m => (S j m : ℂ_[p])) 1 ∧ DualL Dw ((intO ℂ_[p]).subtype.comp s) a (fun j m => (T j m : ℂ_[p])) (fun j m => (S j m : ℂ_[p])) := by
  intro E _ _ _ H Dw p _ s M N a T S hL
  obtain ⟨d, c, θ, hc, hne⟩ := GlobalTheory.T.exists_nonzero_trace_element E
  have hinj := GlobalTheory.ringHom_integers_injective_of_charZero E ℂ_[p] ((intO ℂ_[p]).subtype.comp s)
  have hne' : (intO ℂ_[p]).subtype (s (∑ j, c j * θ j)) ≠ 0 := fun h =>
    hne (hinj (h.trans (map_zero ((intO ℂ_[p]).subtype.comp s)).symm))
  have halt : ∀ x y, Dw.EF x y = -Dw.EF y x := by
    intro x y
    have := Dw.alt (x + y)
    simp only [map_add, LinearMap.add_apply, Dw.alt] at this
    linarith
  have hd : ∀ i j, ∑ m, ∑ m', (S i m : ℂ_[p]) * (T j m' : ℂ_[p]) * ((Dw.EF (a m) (a m') : ℤ) : ℂ_[p]) =
      if i = j then 1 else 0 := by
    intro i j
    have h := congrArg (intO ℂ_[p]).subtype (hL.2.1 i j)
    simp only [map_sum, map_mul, map_intCast, Subring.subtype_apply] at h
    rw [h]
    split_ifs <;> simp
  have hsp : ∀ y, IsEigL Dw ((intO ℂ_[p]).subtype.comp s) y →
      ∃ cf : Fin N → ℂ_[p], ∑ j, cf j • ∑ m, (T j m : ℂ_[p]) ⊗ₜ[ℤ] a m = y := by
    intro y hy
    exact (Submodule.mem_span_range_iff_exists_fun ℂ_[p]).1
      (UpperTheory.CutDual.span_of_casimir (intO ℂ_[p]).subtype s a T hL.2.2 c θ hc hne' y hy)
  have hco := UpperTheory.CutDual.coeff_eq Dw.EF halt a (fun j m => (T j m : ℂ_[p])) (fun j m => (S j m : ℂ_[p])) hd
  refine ⟨⟨fun j m => (S j m).2, fun y hy => ⟨fun h b => ?_, fun h j => ?_⟩⟩, fun y y' hy' => ?_⟩
  · obtain ⟨cf, rfl⟩ := hsp y hy
    rw [_root_.one_mul]
    refine UpperTheory.CutDual.norm_pair_le Dw.EF a (fun j m => (T j m : ℂ_[p])) (fun j m => (T j m).2) cf (fun j => ?_) b
    have h1 := h j
    unfold pr at h1
    rwa [hco cf j, norm_neg] at h1
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun m _ => ?_
    rw [norm_mul]
    have h1 := h (a m)
    rw [_root_.one_mul] at h1
    exact mul_le_one₀ (S j m).2 (norm_nonneg _) h1
  · obtain ⟨cf, rfl⟩ := hsp y' hy'
    unfold pr
    rw [← UpperTheory.CutDual.pair_eq Dw.EF a (fun j m => (T j m : ℂ_[p])) cf y]
    exact Finset.sum_congr rfl fun j _ => by rw [hco cf j]
