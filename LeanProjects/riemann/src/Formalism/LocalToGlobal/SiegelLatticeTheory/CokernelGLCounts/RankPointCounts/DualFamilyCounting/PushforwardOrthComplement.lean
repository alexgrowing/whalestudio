import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFixPushIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LamGEqOneOfOrtho
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.HermitianLattices.HermitianLatticesProofs.AutFinite
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G9

theorem cJof_cast {F : Type} [Field F] {n n' : ℕ} (e : n' = n) (𝔭 : Ideal (𝓞 F)) (a : Fin n → 𝓞 F) :
    cJof 𝔭 (fun i : Fin n' => a (Fin.cast e i)) = cJof 𝔭 a := by
  subst e
  rfl

theorem vJof_cast {F : Type} [Field F] {n n' : ℕ} (e : n' = n) (𝔭 : Ideal (𝓞 F)) (a : Fin n → 𝓞 F) :
    vJof 𝔭 (fun i : Fin n' => a (Fin.cast e i)) = vJof 𝔭 a := by
  subst e
  rfl

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}

theorem isTotPosDef_formOn (hpos : PosDefOn h (orthK h U)) :
    IsTotPosDef (formOn h (orthK h U)) :=
  fun x hx φ => hpos x x.2 (fun e => hx (Subtype.ext e)) φ

theorem jordan_data (h1 : JordanExists) (h5 : AlphaDisc) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hnd : Nondeg h) (hc : IsCompl U (orthK h U)) (hpos : PosDefOn h (orthK h U))
    (T : Submodule (𝓞 K) ↥(orthK h U)) (hT : Submodule.IsLattice K T)
    (hTi : Formalism.HermitianLatticesTheory.IsIntegralLat (formOn h (orthK h U)) T) (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsMaximal) :
    vJ h (orthK h U) (push _ T) 𝔭 = vd (formOn h (orthK h U)) T 𝔭 ∧
    alphaL (formOn h (orthK h U)) T 𝔭 = (discAut h (orthK h U) (push _ T) 𝔭 : ℝ) *
      alphaStd K 𝔭 (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T) 𝔭) ∧
    (vd (formOn h (orthK h U)) T 𝔭 = 0 → cJ h (orthK h U) (push _ T) 𝔭 = 0) := by
  have hWs := formOn_isSymm hs (orthK h U)
  have hWd := isTotPosDef_formOn hpos
  have hex : ∀ b a, IsJordanIn h (orthK h U) (push _ T) 𝔭 b a →
      vJof 𝔭 a = vd (formOn h (orthK h U)) T 𝔭 ∧
      alphaL (formOn h (orthK h U)) T 𝔭 = (discAut h (orthK h U) (push _ T) 𝔭 : ℝ) *
        alphaStd K 𝔭 (finrank K ↥(orthK h U) - cJof 𝔭 a) := by
    intro b a hb
    have hb' := isJordanIn_top h𝔭.isPrime hb
    have e1 := (h1 K F ↥(orthK h U) hK hF (formOn h (orthK h U)) hWs).2 T hT 𝔭 h𝔭 _ _ hb'
    have e2 := h5 K F ↥(orthK h U) hK hF (formOn h (orthK h U)) hWs hWd T hT hTi 𝔭 h𝔭 _ _ hb'
    rw [vJof_cast] at e1
    rw [cJof_cast, ← discAut_push h𝔭.isPrime] at e2
    exact ⟨e1.symm, e2⟩
  obtain ⟨b, a, hb⟩ := (h1 K F V hK hF h hs).1 (orthK h U) (push _ T) (nondegenerate_on_orth_compl hs hnd hc)
    ((isLatIn_push_iff_isLattice T).2 hT) ((isIntegralLat_push T).2 hTi) 𝔭 h𝔭
  have hvJ : vJ h (orthK h U) (push _ T) 𝔭 = vd (formOn h (orthK h U)) T 𝔭 := by
    unfold vJ
    obtain ⟨b', a', hb', e⟩ := Nat.sInf_mem (⟨_, b, a, hb, rfl⟩ :
      Set.Nonempty {v | ∃ b a, IsJordanIn h (orthK h U) (push _ T) 𝔭 b a ∧ v = vJof 𝔭 a})
    rw [e]
    exact (hex b' a' hb').1
  obtain ⟨b₀, a₀, hb₀, e₀⟩ := Nat.sInf_mem (⟨_, b, a, hb, rfl⟩ :
    Set.Nonempty {c | ∃ b a, IsJordanIn h (orthK h U) (push _ T) 𝔭 b a ∧ c = cJof 𝔭 a})
  have hcJ : cJ h (orthK h U) (push _ T) 𝔭 = cJof 𝔭 a₀ := e₀
  refine ⟨hvJ, by rw [hcJ]; exact (hex b₀ a₀ hb₀).2, fun hv => ?_⟩
  rw [hcJ]
  have h0 := (hex b₀ a₀ hb₀).1
  rw [hv] at h0
  unfold vJof at h0
  unfold cJof
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ hi
  exact hi ((Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ _))

theorem mem_of_isLatIn {X : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn X T) :
    ∀ v ∈ T, v ∈ X := fun _ hv => hT.2 ▸ Submodule.subset_span hv

theorem genusMassW_of (h1 : JordanExists) (h5 : AlphaDisc) : GenusMassW := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hc hpos T₀ hT₀ hT₀i c hmc
  obtain ⟨T', rfl⟩ : ∃ T', push (orthK h U) T' = T₀ := ⟨_, push_pull (mem_of_isLatIn hT₀)⟩
  have hT' : Submodule.IsLattice K T' := (isLatIn_push_iff_isLattice T').1 hT₀
  have hT'i := (isIntegralLat_push T').1 hT₀i
  have hWs := formOn_isSymm hs (orthK h U)
  have hWd := isTotPosDef_formOn hpos
  have hMB := Formalism.HermitianLatticesTheory.massBasic K ↥(orthK h U) (formOn h (orthK h U)) hWs (StabilizerLattices.trace_pos hWd) T' hT'
  obtain ⟨s', hs'⟩ := hMB.1
  have hmass := hMB.2.1 s' hs'
  have hMpos := hMB.2.2
  have hMC := hmc ↥(orthK h U) (formOn h (orthK h U)) T' hWs hWd rfl hT' hT'i
  refine ⟨s'.image (push (orthK h U)), ?_, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hT
    have hg := hs'.1 N hN
    exact ⟨(isLatIn_push_iff_isLattice N).2 hg.1, (sameGenusFix_push_iff hK hF hs hc T' N).2 hg.2⟩
  · intro T hT hgen
    obtain ⟨N, rfl⟩ : ∃ N, push (orthK h U) N = T := ⟨_, push_pull (mem_of_isLatIn hT)⟩
    have hN : N ∈ Formalism.HermitianLatticesTheory.genus (formOn h (orthK h U)) T' :=
      ⟨(isLatIn_push_iff_isLattice N).1 hT, (sameGenusFix_push_iff hK hF hs hc T' N).1 hgen⟩
    obtain ⟨N₁, ⟨hN₁, g, hg, hgN⟩, huniq⟩ := hs'.2 N hN
    refine ⟨push _ N₁, ⟨Finset.mem_image_of_mem _ hN₁, extId hc g, extId_mem hs hc hg, ?_⟩, ?_⟩
    · rw [gmap_extId_push hs hc hg, hgN]
    · rintro T₂ ⟨hT₂, g₂, hg₂, e₂⟩
      obtain ⟨N₂, hN₂, rfl⟩ := Finset.mem_image.mp hT₂
      have e : N₂ = N₁ := huniq N₂ ⟨hN₂, restr hg₂, restr_mem hg₂,
        push_injective _ (by rw [← gmap_push hg₂, e₂])⟩
      rw [e]
  · intro T hT _
    obtain ⟨N, rfl⟩ : ∃ N, push (orthK h U) N = T := ⟨_, push_pull (mem_of_isLatIn hT)⟩
    have hfin := Formalism.HermitianLatticesTheory.autFinite K ↥(orthK h U) (formOn h (orthK h U)) hWs (StabilizerLattices.trace_pos hWd) N
      ((isLatIn_push_iff_isLattice N).1 hT)
    have : Finite ↥(Formalism.ThetaLiftIndependence.autL (formOn h (orthK h U)) N) := hfin.to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (stabEquivW hs hc N).symm)
  · rw [Finset.sum_image (fun x _ y _ e => push_injective _ e)]
    simp_rw [card_stab_push hs hc]
    rw [← hmass, hMC]
    have hZ := finite_vd_ne_zero hK hF hWs hWd hT' hT'i
    set Z := hZ.toFinset with hZdef
    have hout : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ Z →
        vd (formOn h (orthK h U)) T' 𝔭.1 = 0 := fun 𝔭 h𝔭 => by
      rw [hZdef, Set.Finite.mem_toFinset] at h𝔭
      exact not_not.mp h𝔭
    have hjd := fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
      jordan_data h1 h5 hK hF hs hnd hc hpos T' hT' hT'i 𝔭.1 𝔭.2
    have hlam : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
        lamP (formOn h (orthK h U)) T' 𝔭.1 =
          alphaStd K 𝔭.1 (finrank K ↥(orthK h U)) *
            (Ideal.absNorm 𝔭.1 : ℝ) ^ (finrank K ↥(orthK h U) * vd (formOn h (orthK h U)) T' 𝔭.1) /
          ((discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) *
            alphaStd K 𝔭.1 (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T') 𝔭.1)) := by
      intro 𝔭
      unfold lamP
      rw [(hjd 𝔭).2.1]
    have hD1 : ∀ 𝔭 ∉ Z, discAut h (orthK h U) (push _ T') 𝔭.1 = 1 := by
      intro 𝔭 h𝔭
      have hv := hout 𝔭 h𝔭
      have hl := localMassFactor_of_valuation_eq_zero hK hF hWs hWd hT' hT'i 𝔭.2 hv
      rw [hlam 𝔭, hv, (hjd 𝔭).2.2 hv, Nat.sub_zero, mul_zero, pow_zero, mul_one] at hl
      have hA := (alphaStd_pos hK hF 𝔭.2 (finrank K ↥(orthK h U))).ne'
      have hDA : (discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) *
          alphaStd K 𝔭.1 (finrank K ↥(orthK h U)) ≠ 0 := fun e => by
        rw [e, div_zero] at hl
        exact zero_ne_one hl
      have e := (div_eq_one_iff_eq hDA).mp hl
      have e' : (discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) = 1 :=
        mul_right_cancel₀ hA (by rw [one_mul]; exact e.symm)
      exact_mod_cast e'
    have e1 : ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, discAut h (orthK h U) (push _ T') 𝔭.1 =
        ∏ 𝔭 ∈ Z, discAut h (orthK h U) (push _ T') 𝔭.1 := tprod_eq_prod hD1
    have e2 : lamG F (formOn h (orthK h U)) T' = ∏ 𝔭 ∈ Z, lamP (formOn h (orthK h U)) T' 𝔭.1 := by
      unfold lamG
      exact tprod_eq_prod fun 𝔭 h𝔭 => localMassFactor_of_valuation_eq_zero hK hF hWs hWd hT' hT'i 𝔭.2 (hout 𝔭 h𝔭)
    have e3 : nM F h (orthK h U) (push _ T') =
        ∏ 𝔭 ∈ Z, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd (formOn h (orthK h U)) T' 𝔭.1 := by
      unfold nM
      simp_rw [fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => (hjd 𝔭).1]
      exact tprod_eq_prod fun 𝔭 h𝔭 => by rw [hout 𝔭 h𝔭, pow_zero]
    have e4 : ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, alphaStd K 𝔭.1 (finrank K ↥(orthK h U)) /
          alphaStd K 𝔭.1 (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T') 𝔭.1) =
        ∏ 𝔭 ∈ Z, alphaStd K 𝔭.1 (finrank K ↥(orthK h U)) /
          alphaStd K 𝔭.1 (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T') 𝔭.1) :=
      tprod_eq_prod fun 𝔭 h𝔭 => by
        rw [(hjd 𝔭).2.2 (hout 𝔭 h𝔭), Nat.sub_zero,
          div_self (alphaStd_pos hK hF 𝔭.2 (finrank K ↥(orthK h U))).ne']
    have hDne : ∀ 𝔭 ∈ Z, (discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) ≠ 0 := by
      intro 𝔭 h𝔭 e
      have h0 : lamP (formOn h (orthK h U)) T' 𝔭.1 = 0 := by rw [hlam 𝔭, e, zero_mul, div_zero]
      have : Formalism.HermitianLatticesTheory.mass (formOn h (orthK h U)) T' = 0 := by
        rw [hMC, e2, Finset.prod_eq_zero h𝔭 h0, mul_zero]
      linarith
    have key : ∀ 𝔭 ∈ Z, (discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) * lamP (formOn h (orthK h U)) T' 𝔭.1 =
        ((Ideal.absNorm 𝔭.1 : ℝ) ^ vd (formOn h (orthK h U)) T' 𝔭.1) ^ finrank K ↥(orthK h U) *
          (alphaStd K 𝔭.1 (finrank K ↥(orthK h U)) /
            alphaStd K 𝔭.1 (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T') 𝔭.1)) := by
      intro 𝔭 h𝔭
      have hB := (alphaStd_pos hK hF 𝔭.2
        (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T') 𝔭.1)).ne'
      rw [hlam 𝔭, ← pow_mul, mul_comm (vd _ _ _) (finrank K _)]
      field_simp [hDne 𝔭 h𝔭, hB]
    rw [e1, e2, e3, e4, Nat.cast_prod, ← Finset.prod_pow]
    calc (∏ 𝔭 ∈ Z, (discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ)) *
          (c * ∏ 𝔭 ∈ Z, lamP (formOn h (orthK h U)) T' 𝔭.1)
        = c * ∏ 𝔭 ∈ Z, ((discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) *
            lamP (formOn h (orthK h U)) T' 𝔭.1) := by
          rw [Finset.prod_mul_distrib]
          ring
      _ = _ := by
          rw [Finset.prod_congr rfl key, Finset.prod_mul_distrib]
          ring

end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

namespace Formalism.L2.SG.Pf.Cnt

theorem genusMassW_of (h1 : JordanExists) (h5 : AlphaDisc) : GenusMassW :=
  OrthogonalComplementGenusMass.genusMassW_of h1 h5

theorem glueMass_of' (h1 : JordanExists) (h2 : JordanInv) (h5 : AlphaDisc) (h6 : GlueLoc)
    (h8 : GlueProd) : GlueMass :=
  glueMass_of h1 h2 h6 h8 (OrthogonalComplementGenusMass.genusMassW_of h1 h5)

end Formalism.L2.SG.Pf.Cnt
