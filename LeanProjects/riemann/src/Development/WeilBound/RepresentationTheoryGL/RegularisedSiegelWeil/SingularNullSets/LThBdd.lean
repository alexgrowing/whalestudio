import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddA
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddD

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ} {W : HSp D} {θ : InfFam D} {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)}

theorem bound_all {v : Pl D} (U : Subgroup (G D n)) (hUo : IsOpen (U : Set (G D n))) (Φ : schwartzA θ W.rank n)
    (hrat : ∀ γ ∈ GF D n, ∀ g h, theta ω Φ (γ * g) h = theta ω Φ g h)
    (hfix : ∀ k ∈ U, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ω k Φ = Φ)
    (hU : ∀ k k' : G D n, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v k = GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v k' →
      k ∈ U → k' ∈ U)
    (hdec : ∀ g : G D n, ∃ γ ∈ GF D n, ∃ g' : G D n, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g' = 1 ∧
      ∃ k ∈ U, k ∈ atPts D.sp.cm.sig (Jst D n) {v} ∧ g = γ * g' * k)
    (hb : ∀ Q : Set (G D n), IsCompact Q → ∃ b : ℝ, ∀ g ∈ Q, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1 →
      ∀ h, ‖theta ω Φ g h‖ ≤ b)
    (K₀ : Set (G D n)) (hK₀ : IsCompact K₀) : ∃ b : ℝ, ∀ g ∈ K₀, ∀ h, ‖theta ω Φ g h‖ ≤ b := by
  have hred : ∀ γ ∈ GF D n, ∀ g' k, k ∈ U → k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ h,
      theta ω Φ (γ * g' * k) h = theta ω Φ g' h := by
    intro γ hγ g' k hk hkv h
    rw [mul_assoc, hrat γ hγ]
    unfold theta
    rw [map_mul, Module.End.mul_apply, hfix k hk hkv]
  choose γf hγf g'f hg'f kf hkf hkvf hgf using hdec
  obtain ⟨W₀, hW₀c, hW₀1, hW₀U⟩ := exists_compact_subset hUo (one_mem U)
  have hW₀n : W₀ ∈ 𝓝 (1 : G D n) := mem_interior_iff_mem_nhds.1 hW₀1
  have hN : ∀ g₀ : G D n, {g | g₀⁻¹ * g ∈ W₀} ∈ 𝓝 g₀ := fun g₀ =>
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW₀n)
  obtain ⟨t, -, hcov⟩ := hK₀.elim_nhds_subcover (fun g₀ => {g | g₀⁻¹ * g ∈ W₀}) fun g₀ _ => hN g₀
  let τ : G D n → G D n := fun ε => ε * (locPart v ε)⁻¹
  have hτ : Continuous τ := continuous_id.mul ((continuous_locPart v).inv)
  let Q : Set (G D n) := ⋃ g₀ ∈ t, (fun ε => g'f g₀ * τ ε) '' W₀
  have hQ : IsCompact Q := t.isCompact_biUnion fun g₀ _ => hW₀c.image (continuous_const.mul hτ)
  obtain ⟨b, hb'⟩ := hb Q hQ
  refine ⟨b, fun g hg h => ?_⟩
  obtain ⟨g₀, hg₀t, hgg₀⟩ := Set.mem_iUnion₂.1 (hcov hg)
  set ε := g₀⁻¹ * g with hε
  have hεW : ε ∈ W₀ := hgg₀
  set εv := locPart v ε with hεv
  set ε' := τ ε with hε'
  have hpv : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v ε' = 1 := by
    show GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v (ε * (locPart v ε)⁻¹) = 1
    rw [map_mul, map_inv, proj_locPart, mul_inv_cancel]
  have hc : kf g₀ * ε' = ε' * kf g₀ := commute_of_atPts (hkvf g₀) hpv
  have hsplit : ε' * εv = ε := by
    show ε * (locPart v ε)⁻¹ * locPart v ε = ε
    group
  have hkU : kf g₀ * εv ∈ U := mul_mem (hkf g₀) (hU ε εv (proj_locPart v ε).symm (hW₀U hεW))
  have hkv : kf g₀ * εv ∈ atPts D.sp.cm.sig (Jst D n) {v} := mul_mem (hkvf g₀) (locPart_mem_atPts v ε)
  have heq : g = γf g₀ * (g'f g₀ * ε') * (kf g₀ * εv) := by
    calc g = g₀ * ε := by rw [hε]; group
      _ = γf g₀ * g'f g₀ * kf g₀ * (ε' * εv) := by rw [← hgf g₀, hsplit]
      _ = γf g₀ * g'f g₀ * (kf g₀ * ε') * εv := by simp only [mul_assoc]
      _ = γf g₀ * g'f g₀ * (ε' * kf g₀) * εv := by rw [hc]
      _ = _ := by simp only [mul_assoc]
  rw [heq, hred _ (hγf g₀) _ _ hkU hkv]
  refine hb' _ (Set.mem_iUnion₂.2 ⟨g₀, hg₀t, ε, hεW, rfl⟩) ?_ h
  rw [map_mul, hg'f g₀, hpv, one_mul]

end PositivityTheory.Rg.Rsw.L.LThBdd

namespace PositivityTheory.Rg.Rsw.L

open LThBdd in
theorem thBdd : WMaj → LatBound → WeakApproximationFinitePlace → ThBdd := by
  intro hWM hLB hWA D n W ψ hψ χ hχ hη θ hθ μ hμ ω hω nb hnb v C hC Ψ Ψ' hΨ hΨ'
  obtain ⟨𝓕, hμ'⟩ := hμ
  have hW := hWM D n W ψ hψ χ hχ hη θ hθ μ ⟨𝓕, hμ'⟩ ω hω Ψ'
  have hrat : ∀ γ ∈ GF D n, ∀ g h, theta ω Ψ' (γ * g) h = theta ω Ψ' g h :=
    fun γ hγ g h => theta_rat hψ hχ hθ hμ' hω Ψ' hγ g h
  have hfix : ∀ k ∈ Ucut nb v C.s, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ω k Ψ' = Ψ' :=
    fun k hk hkv => fix_open hnb C Ψ Ψ' hΨ hΨ' hk hkv
  refine ⟨theta_cont hθ Ψ' hW.1 hW.2, hrat, ⟨Ucut nb v C.s, isOpen_Ucut _ _ _, hfix⟩, fun K₀ hK₀ => ?_,
    fun x g hg => ⟨omega_cut hω hnb C Ψ Ψ' hΨ' hg, theta_nb hω hnb C hC Ψ Ψ' hΨ hΨ' x hg⟩⟩
  exact bound_all (Ucut nb v C.s) (isOpen_Ucut _ _ _) Ψ' hrat hfix (fun k k' e hk => mem_Ucut_of_proj e hk)
    (fun g => hWA D n v (Ucut nb v C.s) (isOpen_Ucut _ _ _) g)
    (bound_triv hω hnb C hC Ψ Ψ' hΨ hΨ' hLB hθ hW.2) K₀ hK₀

end PositivityTheory.Rg.Rsw.L

end
