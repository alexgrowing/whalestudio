import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFactorizableApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumFiniteDimensionalOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanLevelSubgroupClosedMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfMemSpanImage

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV

noncomputable section

namespace GlobalTheory.PolLocFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {d : ℕ} {W : Spc F E d}

theorem eInf_smul_eq_zero (y : AE F E) (hy : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y = 0) :
    GlobalTheory.KInfGroup.eInf F • y = 0 := by
  have key : ∀ y : AE F E, GlobalTheory.KInfGroup.eInf F • y =
      TensorProduct.map (LinearMap.inl F (Ainf F) (Af F)) (LinearMap.id : E →ₗ[F] E)
        (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero] <;> rfl
    | tmul a e =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]
      congr 1
      refine Prod.ext ?_ ?_
      · show (1 : Ainf F) * a.1 = a.1
        exact one_mul _
      · show (0 : Af F) * a.2 = 0
        exact zero_mul _
    | add x y hx hy =>
      rw [smul_add, hx, hy, map_add, map_add]
      try rfl
  rw [key, hy, map_zero]
  try rfl

theorem finPt_of_mem_finU {b : UA σ W.J} (hb : b ∈ finU σ W.J) : b ∈ GlobalTheory.ThKAdm.FinPt σ W := by
  intro u hu
  have hu2 : u.2 = 0 := hu
  have h1 : ∀ i j, GlobalTheory.KInfGroup.eInf F • (mat b - 1) i j = 0 := by
    intro i j
    apply eInf_smul_eq_zero
    have h := congrFun (congrFun (mem_finU.1 hb) i) j
    rw [Matrix.map_apply] at h
    rw [Matrix.sub_apply, map_sub, h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hu' : u = u * GlobalTheory.KInfGroup.eInf F := by
    refine Prod.ext ?_ ?_
    · show u.1 = u.1 * 1
      exact (mul_one _).symm
    · show u.2 = u.2 * 0
      rw [hu2, mul_zero]
  rw [hu', mul_smul]
  ext i j
  have h2 := h1 i j
  rw [Matrix.sub_apply] at h2
  simp [Matrix.smul_apply, h2]

end GlobalTheory.PolLocFin

namespace GlobalTheory.PolLocFin

theorem exists_open_fix (hKP : GlobalTheory.ThK.KP) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
    (χX χW : Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ)
    (hP : GlobalTheory.ThK.IsPair B M χX χW om r s r' s') :
    ∀ Φ ∈ GlobalTheory.ThK.PolData B M, ∃ U : Subgroup (UA σ W.J), IsOpen (U : Set (UA σ W.J)) ∧
      ∀ k ∈ U, k ∈ finU σ W.J → om (1, k) Φ = Φ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, -, φ, hφ, hv, rfl⟩ := hx
    obtain ⟨U, hU, h⟩ := GlobalTheory.T.exists_open_subgroup_fixing_pure_tensor F E σ B n d X W M χX χW om r s r' s' hKP hP f φ hφ hv
    exact ⟨U, hU, fun k hk hkf => h k hk (mem_finU.1 hkf)⟩
  | zero => exact ⟨⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, fun k _ _ => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, h⟩ := hx
    obtain ⟨V, hV, h'⟩ := hy
    refine ⟨U ⊓ V, by rw [Subgroup.coe_inf]; exact hU.inter hV, fun k hk hkf => ?_⟩
    rw [map_add, h k hk.1 hkf, h' k hk.2 hkf]
  | smul c x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun k hk hkf => by rw [map_smul, h k hk hkf]⟩

theorem polData_locFin : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ Kf : Subgroup (UA σ W.J), IsCompact (Kf : Set (UA σ W.J)) → Kf ≤ finU σ W.J → ∀ Φ ∈ GlobalTheory.ThK.PolData B M, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Subgroup.closure (KInf σ W B.emb ∪ (Kf : Set (UA σ W.J))) => om (1, (k : UA σ W.J)) Φ)) := by
  classical
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Kf hKc hKf Φ hΦ
  obtain ⟨hTG, -, -, -⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ d W.J
  have hK := GlobalTheory.kInf_one_mul_commute_finPt F E σ d W B.emb

  obtain ⟨S, hS, hSP, hSk⟩ := GlobalTheory.T.polynomial_datum_finite_dimensional_orbit F E σ B n d X W M χX χW om r s r' s' hKP hP Φ hΦ
  haveI : FiniteDimensional ℂ S := hS

  have hfix := exists_open_fix hKP F E σ B n d X W M χX χW om r s r' s' hP
  have hfin : ∀ t : Finset (GlobalTheory.ThK.Fn F n d), (∀ x ∈ t, x ∈ GlobalTheory.ThK.PolData B M) →
      ∃ U : Subgroup (UA σ W.J), IsOpen (U : Set (UA σ W.J)) ∧
        ∀ x ∈ t, ∀ k ∈ U, k ∈ finU σ W.J → om (1, k) x = x := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro _
      exact ⟨⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, fun x hx => by simp at hx⟩
    · intro a t _ ih h
      obtain ⟨U, hU, hU'⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
      obtain ⟨V, hV, hV'⟩ := hfix a (h a (Finset.mem_insert_self a t))
      refine ⟨U ⊓ V, by rw [Subgroup.coe_inf]; exact hU.inter hV, fun x hx k hk hkf => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hV' k hk.2 hkf
      · exact hU' x hx k hk.1 hkf
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional S).2 hS
  obtain ⟨U, hU, hU'⟩ := hfin t (fun x hx => hSP (ht ▸ Submodule.subset_span hx))
  have hSfix : ∀ x ∈ S, ∀ k ∈ U, k ∈ finU σ W.J → om (1, k) x = x := by
    intro x hx k hk hkf
    rw [← ht] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hU' y hy k hk hkf
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add, hy, hz]
    | smul c y _ hy => rw [map_smul, hy]

  obtain ⟨C, hCK, hCfin, hcover⟩ := hKc.elim_finite_subcover_image
    (b := (Kf : Set (UA σ W.J))) (c := fun c => (fun x => c⁻¹ * x) ⁻¹' (U : Set (UA σ W.J)))
    (fun c _ => hU.preimage (continuous_const.mul continuous_id))
    (fun b hb => Set.mem_iUnion₂.2 ⟨b, hb, by simp [U.one_mem]⟩)
  haveI : Finite C := hCfin.to_subtype
  set T : Submodule ℂ (GlobalTheory.ThK.Fn F n d) := ⨆ c : C, S.map (om (1, (c : UA σ W.J))) with hT
  haveI : FiniteDimensional ℂ T := Submodule.finiteDimensional_iSup _

  have hdec : ∀ g ∈ Subgroup.closure (KInf σ W B.emb ∪ (Kf : Set (UA σ W.J))),
      ∃ b ∈ Kf, ∃ a ∈ KInf σ W B.emb, g = b * a := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨1, Kf.one_mem, x, hx, (one_mul x).symm⟩
      · exact ⟨x, hx, 1, hK.1, (mul_one x).symm⟩
    | one => exact ⟨1, Kf.one_mem, 1, hK.1, (mul_one 1).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨b, hb, a, ha, rfl⟩ := hx
      obtain ⟨b', hb', a', ha', rfl⟩ := hy
      have hc : b' * a = a * b' := hK.2.2 b' (finPt_of_mem_finU (hKf hb')) a ha
      refine ⟨b * b', Kf.mul_mem hb hb', a * a', hK.2.1 a ha a' ha', ?_⟩
      have e : b * a * (b' * a') = b * (a * b') * a' := by simp only [mul_assoc]
      rw [e, ← hc]
      simp only [mul_assoc]
    | inv x _ hx =>
      obtain ⟨b, hb, a, ha, rfl⟩ := hx
      refine ⟨b⁻¹, Kf.inv_mem hb, a⁻¹, GlobalTheory.ThetaFacCompl.inv_mem_KInf B.emb ha, ?_⟩
      rw [mul_inv_rev]
      exact (hK.2.2 b⁻¹ (finPt_of_mem_finU (hKf (Kf.inv_mem hb))) a⁻¹
        (GlobalTheory.ThetaFacCompl.inv_mem_KInf B.emb ha)).symm
  refine Submodule.finiteDimensional_of_le (S₂ := T) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  obtain ⟨b, hb, a, ha, hk⟩ := hdec k k.2
  have hs : om (1, a) Φ ∈ S := hSk a ha
  obtain ⟨c, hcC, hbc⟩ := Set.mem_iUnion₂.1 (hcover hb)
  have hbc' : c⁻¹ * b ∈ U := hbc
  have hcf : c⁻¹ * b ∈ finU σ W.J := (finU σ W.J).mul_mem ((finU σ W.J).inv_mem (hKf (hCK hcC))) (hKf hb)
  have e1 : ((1 : UA σ X.J), (k : UA σ W.J)) = (1, c) * ((1, c⁻¹ * b) * (1, a)) := by
    refine Prod.ext ?_ ?_
    · show (1 : UA σ X.J) = 1 * (1 * 1)
      simp
    · show (k : UA σ W.J) = c * ((c⁻¹ * b) * a)
      rw [hk, ← mul_assoc, mul_inv_cancel_left]
  show om (1, (k : UA σ W.J)) Φ ∈ T
  rw [e1, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hSfix _ hs _ hbc' hcf]
  exact Submodule.mem_iSup_of_mem (⟨c, hcC⟩ : C) (Submodule.mem_map_of_mem hs)

end GlobalTheory.PolLocFin
