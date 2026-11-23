import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineStabilizerOrthogonalActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineStabilizerOrthogonalUniqueStatement

noncomputable section

namespace GlobalTheory.IwDecompAdapted
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.IwLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem iwasawa_reS (B : Base F E) {n n₁ : ℕ} {X Y : Spc F E n} {X₁ : Spc F E n₁} {r s : ℕ} {H : Plane E n n₁}
    {i₀ i₁ : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B (reS X Y) X₁ i₀ i₁)
    (K : Subgroup (UA σ X.J)) (hK : IsStab (X := X) B K) (g : UA σ X.J) :
    ∃ p ∈ lineStab σ X.J H.x, ∃ k ∈ K, g = p * k := by
  classical
  haveI : X.L.IsLattice E := hX.lat
  have hσ : IsCMExt F E σ := hB.cm
  have hs : ∀ z : E, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hσ.2.2.2, hσ.2.2.2, star_star])
  have hND : IsHermND σ X.Jᵀ := isHermND_transpose hX
  have hHxx : form σ X.J H.x H.x = 0 := hH.xx
  have hHyy : form σ X.J H.y H.y = 0 := hH.yy
  have hHxy : form σ X.J H.x H.y = 1 := hH.xy
  set xc : Matrix (Fin n) (Fin 1) E := Matrix.of fun i _ => H.x i with hxc
  set yc : Matrix (Fin n) (Fin 1) E := Matrix.of fun i _ => H.y i with hyc
  have hfyx : form σ X.J H.y H.x = 1 := by
    have e : form σ X.J H.y H.x = σ (form σ X.J H.x H.y) := by
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hs, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [← hX.herm k l, hs]; ring
    rw [e, hHxy, map_one]
  have hxx : cT (σ : E →+* E) xc * X.Jᵀ * xc = 0 := by
    rw [cT_col_eq_form]; ext i j; simp [hHxx]
  have hyy : cT (σ : E →+* E) yc * X.Jᵀ * yc = 0 := by
    rw [cT_col_eq_form]; ext i j; simp [hHyy]
  have hxy : cT (σ : E →+* E) xc * X.Jᵀ * yc = 1 := by
    rw [cT_col_eq_form]; ext i j; rw [Subsingleton.elim i j]; simp [hfyx]
  have hyx : cT (σ : E →+* E) yc * X.Jᵀ * xc = 1 := by
    rw [cT_col_eq_form]; ext i j; rw [Subsingleton.elim i j]; simp [hHxy]
  have hSD := GlobalTheory.T.hermitian_lattice_self_dual_everywhere F E σ B n X r s hB hX
  have loc : ∀ v (y : GLoc σ X.Jᵀ v), ∃ q k : GLoc σ X.Jᵀ v, k ∈ stabLoc σ X.Jᵀ X.L v ∧ y = q * k ∧
      ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ X.Jᵀ q).1 * xc.map (inclR (F := F) (Fv F v)) =
        xc.map (inclR (F := F) (Fv F v)) * β.1 := fun v y =>
    if hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v then
      GlobalTheory.T.hyperbolic_pair_lattice_local_split F E σ hσ n X.Jᵀ hND xc yc hxx hyy hxy hyx X.L hX.lat v hv (hSD v) y
    else GlobalTheory.T.isotropic_vector_lattice_local F E σ hσ hB.unram n X.Jᵀ hND xc yc hxx hyx X.L hX.lat v hv (hSD v) y
  obtain ⟨a, ha, haK⟩ := GlobalTheory.T.majorant_frame_commutes_cartan F E σ B n X r s hB hX
  set g' := (ofGAd σ X.J).symm g with hg'
  choose qa ka hka hga βa hβa using fun w => GlobalTheory.T.archimedean_iwasawa_majorant_frame F E σ hσ n X.Jᵀ hND xc yc hxx hyx a ha w
    (projArch σ X.Jᵀ w g')
  choose qf kf hkf hgf βf hβf using fun v => loc v (proj σ X.Jᵀ v g')
  set S := (Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ X.Jᵀ X.L g')).toFinset with hS
  obtain ⟨pa, hpa1, hpa2⟩ := exists_arch_comp σ X.Jᵀ qa
  obtain ⟨pf, hpf1, hpf2⟩ := exists_fin_comp σ X.Jᵀ qf S
  set p := pa * pf with hp
  have pA : ∀ w, projArch σ X.Jᵀ w p = qa w := fun w => by rw [hp, map_mul, hpa2 w, hpf1 w, mul_one]
  have pF : ∀ v, proj σ X.Jᵀ v p = if v ∈ S then qf v else 1 := fun v => by rw [hp, map_mul, hpa1 v, hpf2 v, one_mul]
  obtain ⟨l, hl⟩ := GlobalTheory.T.parabolic_archimedean_eigenvector F E σ n X.Jᵀ xc (cT (σ : E →+* E) yc * X.Jᵀ) hyx p
    (fun w => ⟨βa w, by rw [pA w]; exact hβa w⟩) (fun v => by
      rw [pF v]
      split_ifs
      · exact ⟨βf v, hβf v⟩
      · exact ⟨1, by simp⟩)
  have hk : ofGAd σ X.J (p⁻¹ * g') ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X := by
    refine GlobalTheory.T.majorant_stabilizer_iwasawa_line F E σ B n X hX.lat _ (fun w => ?_) (fun v => ?_)
    · have e : projArch σ X.Jᵀ w (p⁻¹ * g') = ka w := by
        rw [map_mul, map_inv, pA w, hga w, inv_mul_cancel_left]
      rw [e]; exact haK w (ka w) (hka w)
    · have e1 : proj σ X.Jᵀ v (p⁻¹ * g') = (if v ∈ S then qf v else 1)⁻¹ * proj σ X.Jᵀ v g' := by
        rw [map_mul, map_inv, pF v]
      rw [e1]
      split_ifs with hv
      · rw [hgf v, inv_mul_cancel_left]; exact hkf v
      · rw [inv_one, one_mul]
        by_contra hc
        exact hv ((Set.Finite.mem_toFinset _).2 hc)
  refine ⟨ofGAd σ X.J p, ⟨l, ?_⟩, ofGAd σ X.J (p⁻¹ * g'), (hK _).2 ((GlobalTheory.StabHaar.isStab_stabK B X _).1 hk), ?_⟩
  · rw [mat_ofGAd]
    funext i
    have := congrFun (congrFun hl i) 0
    simpa [adMat, xc, incV, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  · rw [← map_mul, mul_inv_cancel_left, hg', MulEquiv.apply_symm_apply]

end GlobalTheory.IwDecompAdapted

section Main
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.IwDecompAdapted

theorem levi_part : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ p ∈ GlobalTheory.IwLine.lineStab σ X.J H.x, ∃ g₀ : UA σ X₁.J, ∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat p *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat g₀ *ᵥ z) + a • incV F H.x := by
  intro F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hH p hp
  obtain ⟨G, hG⟩ := GlobalTheory.T.line_stabilizer_orthogonal_action F E σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hH p hp
  obtain ⟨G', hG'⟩ := GlobalTheory.T.line_stabilizer_orthogonal_action F E σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hH p⁻¹ (Subgroup.inv_mem _ hp)
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.T.line_stabilizer_orthogonal_unique F E σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hH p hp G G' hG hG'
  exact ⟨g₀, hg₀ ▸ hG⟩

theorem iwasawa_decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ (K : Subgroup (UA σ X.J)), IsStab (X := X) B K → ∀ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, (∀ l g₀, IsLevi (W₁ := X₁) H l g₀ (m l g₀)) → ∀ g : UA σ X.J, ∃ u ∈ unip σ X H, ∃ l g₀, ∃ k ∈ K, g = u * m l g₀ * k := by
  intro F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX _hXY hH K hK m hm g
  obtain ⟨p, hp, k, hk, rfl⟩ := iwasawa_reS B hB hX hH K hK g
  obtain ⟨α, hα⟩ := hp
  obtain ⟨g₀, hg₀⟩ := levi_part F E σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hH p ⟨α, hα⟩
  have mm : ∀ a b : UA σ X.J, mat (a * b) = mat a * mat b := fun _ _ => rfl
  have mm₁ : ∀ a b : UA σ X₁.J, mat (a * b) = mat a * mat b := fun _ _ => rfl
  have m1 : mat (1 : UA σ X.J) = 1 := rfl
  have m1₁ : mat (1 : UA σ X₁.J) = 1 := rfl
  obtain ⟨hx, -, hι⟩ := hm α g₀
  have hx' : mat (m α g₀)⁻¹ *ᵥ incV F H.x = (α⁻¹).1 • incV F H.x := by
    have e := congrArg (fun v => (α⁻¹).1 • (mat (m α g₀)⁻¹ *ᵥ v)) hx
    simp only [Matrix.mulVec_mulVec, ← mm, inv_mul_cancel, m1, Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul,
      Units.inv_mul, one_smul] at e
    exact e.symm
  have hι' : mat (m α g₀)⁻¹ * incM F H.ι = incM F H.ι * mat g₀⁻¹ := by
    calc mat (m α g₀)⁻¹ * incM F H.ι = mat (m α g₀)⁻¹ * incM F H.ι * (mat g₀ * mat g₀⁻¹) := by
          rw [← mm₁, mul_inv_cancel, m1₁, Matrix.mul_one]
      _ = mat (m α g₀)⁻¹ * (mat (m α g₀) * incM F H.ι) * mat g₀⁻¹ := by
          rw [hι]; simp only [Matrix.mul_assoc]
      _ = incM F H.ι * mat g₀⁻¹ := by
          rw [← Matrix.mul_assoc, ← mm, inv_mul_cancel, m1, Matrix.one_mul]
  refine ⟨p * (m α g₀)⁻¹, Subgroup.subset_closure ⟨?_, fun z => ?_⟩, α, g₀, k, hk, by group⟩
  · rw [mm, ← Matrix.mulVec_mulVec, hx', Matrix.mulVec_smul, hα, smul_smul, Units.inv_mul, one_smul]
  · obtain ⟨a, ha⟩ := hg₀ (mat g₀⁻¹ *ᵥ z)
    refine ⟨a, ?_⟩
    have e1 : mat (m α g₀)⁻¹ *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat g₀⁻¹ *ᵥ z) := by
      rw [Matrix.mulVec_mulVec, hι', ← Matrix.mulVec_mulVec]
    have e2 : mat g₀ *ᵥ (mat g₀⁻¹ *ᵥ z) = z := by
      rw [Matrix.mulVec_mulVec, ← mm₁, mul_inv_cancel, m1₁, Matrix.one_mulVec]
    rw [mm, ← Matrix.mulVec_mulVec, e1, ha, e2]

end GlobalTheory.IwDecompAdapted
end Main
