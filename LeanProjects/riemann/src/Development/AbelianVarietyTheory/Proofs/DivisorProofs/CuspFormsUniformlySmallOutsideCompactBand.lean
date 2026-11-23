import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFormsEquicontinuousOnBandStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.ReductionSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompactDetBandSiegelSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjArchUnipotentMemNhdsOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalNormLeOfOscillationScaledUnipFDStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

noncomputable section
namespace GlobalTheory.HCF.Tail

theorem compactPart : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ω : Set (GA E a)), IsCompact ω →
    ∀ t R : ℝ, 0 < t → ∃ C : Set (GA E a), IsCompact C ∧ C ⊆ band E a ∧
      ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i),
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ R * ρ j) →
        ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ band E a →
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ C := GlobalTheory.T.exists_isCompact_detBand_siegelSet

theorem finConj : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ ω : Set (GA E a), IsCompact ω →
    ∃ M : ℕ, 0 < M ∧ ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
      ∀ z : BlockIx a r → Ad E, (∀ p, (z p).1 = 0) →
      (∀ p, ∃ c ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, (z p).2 = (M : Af E) * c) →
      ∃ l ∈ L, (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k)⁻¹ * unip z *
        (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k) = finGL E a l := GlobalTheory.T.exists_conj_finiteUnipotent_mem_openSubgroup

theorem infConj : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (U : Set (GA E a)), U ∈ 𝓝 (1 : GA E a) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : GA E a) (P : BlockIx a r → Ad E), (∀ p, (P p).2 = 0) →
      ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E)))‖ ≤ δ →
      x⁻¹ * unip P * x ∈ U := GlobalTheory.T.conj_archUnipotent_mem_nhds_one

theorem meanZero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (B : ℝ),
      (∀ X ∈ GroundTheory.Automorphic.scaledUnipFD E a r M, ‖φ (unip X * x) - φ x‖ ≤ B) → ‖φ x‖ ≤ B := GlobalTheory.T.cuspidal_norm_le_of_oscillation_scaledUnipFD

section Band
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem absDetA_mul (g h : GA E a) : absDetA (g * h) = absDetA g * absDetA h := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E), GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E),
    GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E), map_mul, map_mul]
  rfl

theorem absDetA_ratGL (γ : GL (Fin a) E) : absDetA (ratGL E a γ) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (ratGL E a γ) = GroundTheory.Global.IdeleGroup.diagonal E (Matrix.GeneralLinearGroup.det γ) :=
    Units.ext (det_map _ γ)
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E), h, GroundTheory.Global.IdeleGroup.ideleModule_diagonal]
  rfl

theorem absDetA_unip {r : ℕ} (P : BlockIx a r → Ad E) : absDetA (unip P) = 1 := by
  unfold absDetA
  rw [det_unip]
  simpa [absDetA] using (absDetA_one (E := E) (a := a))

theorem absDetA_conj (x u : GA E a) (hu : absDetA u = 1) : absDetA (x * (x⁻¹ * u * x)) = absDetA x := by
  have h1 : absDetA x⁻¹ * absDetA x = 1 := by rw [← absDetA_mul, inv_mul_cancel, absDetA_one]
  rw [absDetA_mul, absDetA_mul, absDetA_mul, hu, mul_one, h1, mul_one]

theorem mem_band_ratGL_mul {γ : GL (Fin a) E} {g : GA E a} (hg : g ∈ band E a) : ratGL E a γ * g ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, absDetA_mul, absDetA_ratGL, one_mul] at hg ⊢
  exact hg

end Band

section Span
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {L : Subgroup (GL (Fin a) (Af E))}
  {W : Submodule ℂ (Kinf E a → ℂ)} {X : Set (Module.End ℂ (Sm E a) → ℂ)} {N : ℕ}

theorem span_left {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx.1.left
  | zero => intro γ g; rfl
  | add x y _ _ hx hy => intro γ g; simp [hx γ g, hy γ g]
  | smul c x _ hx => intro γ g; simp [hx γ g]

theorem span_fin {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    ∀ l ∈ L, finRep E a l φ = φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx.2.1
  | zero => intro l _; exact map_zero _
  | add x y _ _ hx hy => intro l hl; rw [map_add, hx l hl, hy l hl]
  | smul c x _ hx => intro l hl; rw [map_smul, hx l hl]

theorem span_right {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) {l : GL (Fin a) (Af E)} (hl : l ∈ L)
    (g : GA E a) : φ.1 (g * finGL E a l) = φ.1 g :=
  congrFun (congrArg Subtype.val (span_fin hφ l hl)) g

theorem span_cont (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) : Continuous φ.1 := by
  refine GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E a φ ?_
  refine isOpen_iff_forall_mem_open.2 fun k hk => ⟨(fun l => k * l) '' (L : Set (GL (Fin a) (Af E))), ?_, ?_, ⟨1, L.one_mem, mul_one k⟩⟩
  · rintro _ ⟨l, hl, rfl⟩
    change finRep E a (k * l) φ = φ
    rw [map_mul, Module.End.mul_apply, span_fin hφ l hl]
    exact hk
  · exact (Homeomorph.mulLeft k).isOpenMap _ hL

end Span

open GroundTheory.Automorphic.Reduction in
theorem oneRoot (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) (W : Submodule ℂ (Kinf E a → ℂ)) (hW : FiniteDimensional ℂ W)
    (X : Set (Module.End ℂ (Sm E a) → ℂ)) (hX : X.Finite) (N : ℕ)
    {ω : Set (GA E a)} (hω : IsCompact ω) (hωB : ω ⊆ (adelicBorel (K := E) (n := a) : Set (GA E a)))
    {t : ℝ} (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) {r : ℕ} (hr : 0 < r) (hra : r < a) :
    ∃ R : ℝ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) →
      ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ k ∈ (maxCompact (K := E) (n := a)),
      b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k ∈ band E a →
      R * ρ ⟨r, hra⟩ ≤ ρ ⟨r - 1, by omega⟩ →
      ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k)‖ ≤ ε * M := by
  obtain ⟨U, hU, hequi⟩ := GlobalTheory.T.harishChandraForms_equicontinuous_on_band E a L hL W hW X hX N ε hε
  obtain ⟨M₀, hM₀, hfin⟩ := finConj E a r L hL ω hω
  obtain ⟨C₁, hC₁⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_norm_archMat_conj_le hω hωB ht hr hra
    (GroundTheory.Automorphic.isCompact_scaledInfSet (K := E) M₀)
  obtain ⟨δ, hδ, hinf⟩ := infConj E a r U hU
  refine ⟨max C₁ 0 / δ + 1, ?_⟩
  intro φ hφ hcusp M hM b hb ρ hρ hs k hk hband hR
  set x := b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k with hx
  have hq0 : 0 < ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩ := div_pos (hρ _) (hρ _)
  have hgain : C₁ * (ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩) ≤ δ := by
    set q := ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩
    set c := max C₁ 0
    have hc0 : 0 ≤ c := le_max_right _ _
    have hRq : (c / δ + 1) * q ≤ 1 := by
      rw [show q = ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩ from rfl, mul_div_assoc', div_le_one (hρ _)]
      exact hR
    have h1 : C₁ * q ≤ c * q := mul_le_mul_of_nonneg_right (le_max_left _ _) hq0.le
    have h2 : c * q ≤ δ := by
      have e : c = δ * (c / δ) := by field_simp
      nlinarith [mul_nonneg (div_nonneg hc0 hδ.le) hq0.le]
    linarith
  refine meanZero E a r hr hra φ.1 (span_left hφ) hcusp (span_cont hL hφ) M₀ hM₀ x (ε * M) ?_
  intro Y hY
  have hsplit : unip Y * x = x * (x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y) * x) *
      (x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncFin Y) * x) := by
    conv_lhs => rw [← GroundTheory.Automorphic.CuspidalSpectrum.truncInf_add_truncFin Y, unip_add]
    group
  obtain ⟨l, hl, hle⟩ := hfin b hb ρ hρ k hk (GroundTheory.Automorphic.CuspidalSpectrum.truncFin Y) (fun p => rfl)
    (fun p => GroundTheory.Automorphic.exists_finite_eq_natCast_mul hM₀ hY p)
  have hv : x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y) * x ∈ U :=
    hinf x _ (fun p => rfl) ((hC₁ b hb ρ hρ hs k hk (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y) (fun p => rfl)
      (fun p => GroundTheory.Automorphic.infinite_mem_scaledInfSet hM₀ hY p)).trans hgain)
  rw [hsplit, hle, span_right hφ hl]
  refine hequi φ hφ M hM x hband _ hv ?_
  have h := absDetA_conj x (unip (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y)) (absDetA_unip _)
  simp only [band, Set.mem_setOf_eq] at hband ⊢
  rw [h]
  exact hband

open GroundTheory.Automorphic.Reduction in

theorem tails : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W →
    ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : Set (GA E a), IsCompact C ∧
    C ⊆ band E a ∧ ∀ g ∈ band E a, (∃ γ : GL (Fin a) E, ratGL E a γ * g ∈ C) ∨
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) →
      ‖φ.1 g‖ ≤ ε * M := by
  intro E _ _ _ a L hL W hW X hX N ε hε
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := E) a
  have hex : ∀ r : ℕ, ∀ (hr : 0 < r) (hra : r < a), ∃ R : ℝ, _ := fun r hr hra =>
    oneRoot E a L hL W hW X hX N hω hωB ht hε hr hra
  choose Rf hRf using hex
  set R : ℝ := 1 + ∑ r : Fin a, if h : 0 < (r : ℕ) then max (Rf r h r.2) 0 else 0 with hRdef
  have hRle : ∀ (r : ℕ) (hr : 0 < r) (hra : r < a), Rf r hr hra ≤ R := by
    intro r hr hra
    have h1 := Finset.single_le_sum (f := fun r : Fin a => if h : 0 < (r : ℕ) then max (Rf r h r.2) 0 else 0)
      (fun r _ => by split_ifs <;> simp) (Finset.mem_univ ⟨r, hra⟩)
    simp only [hr, dif_pos] at h1
    linarith [le_max_left (Rf r hr hra) 0]
  obtain ⟨C, hC, hCb, hCmem⟩ := compactPart E a ω hω t R ht
  refine ⟨C, hC, hCb, fun g hg => ?_⟩
  obtain ⟨γ, hγ⟩ := hsieg g
  obtain ⟨b, hb, _, ⟨ρ, hρ, hs, rfl⟩, k, hk, he⟩ := hγ
  have he' : ratGL E a γ * g = b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k := he
  have hgb : ratGL E a γ * g ∈ band E a := mem_band_ratGL_mul hg
  by_cases hall : ∀ (r : ℕ) (hr : 0 < r) (hra : r < a), ρ ⟨r - 1, by omega⟩ ≤ R * ρ ⟨r, hra⟩
  · refine Or.inl ⟨γ, ?_⟩
    rw [he'] at hgb ⊢
    refine hCmem b hb ρ hρ hs (fun i j hij => ?_) k hk hgb
    have h1 := hall j (by omega) j.2
    have e : (⟨(j : ℕ) - 1, by omega⟩ : Fin a) = i := Fin.ext (by simp; omega)
    rwa [e] at h1
  · push_neg at hall
    obtain ⟨r, hr, hra, hlt⟩ := hall
    refine Or.inr fun φ hφ hc M hM => ?_
    rw [← span_left hφ γ g, he']
    rw [he'] at hgb
    refine hRf r hr hra φ hφ hc M hM b hb ρ hρ hs k hk hgb ?_
    exact (mul_le_mul_of_nonneg_right (hRle r hr hra) (hρ _).le).trans hlt.le

end GlobalTheory.HCF.Tail

end
