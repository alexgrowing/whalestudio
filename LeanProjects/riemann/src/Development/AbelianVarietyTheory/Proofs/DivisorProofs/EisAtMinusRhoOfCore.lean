import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSqFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerFiniteIndexChainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaHeightAdaptedLatticeStatement
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.EisReduce
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.SquareIntegrability

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem line_iff {σ : E →ₐ[F] E} {n : ℕ} {J J' : Matrix (Fin n) (Fin n) E} (e : UA σ J ≃* GAd σ J')
    (he : ∀ g, matHom _ σ J' (e g) = (g : GL (Fin n) (AF F ⊗[F] E))) (x : Fin n → E) (p : UA σ J) (l : (AF F ⊗[F] E)ˣ) :
    mat p *ᵥ incV F x = l.1 • incV F x ↔
      (matHom _ σ J' (e p)).1 * adMat F (Matrix.of fun i (_ : Fin 1) => x i) =
        l.1 • adMat F (Matrix.of fun i (_ : Fin 1) => x i) := by
  rw [he]
  constructor
  · intro h
    ext i j
    have := congrFun h i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, adMat, incV, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat] using this
  · intro h
    funext i
    have := congrFun (congrFun h i) 0
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, adMat, incV, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat] using this

section Height
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : Matrix (Fin n) (Fin 1) E}
  {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)} {h : GAd σ J → ℝ}

theorem line_mul {p q : GAd σ J} {l l' : (AF F ⊗[F] E)ˣ} (hp : (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x)
    (hq : (matHom _ σ J q).1 * adMat F x = l'.1 • adMat F x) :
    (matHom _ σ J (p * q)).1 * adMat F x = (l * l').1 • adMat F x := by
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hp, smul_smul, Units.val_mul, mul_comm]

theorem line_inv {p : GAd σ J} {l : (AF F ⊗[F] E)ˣ} (hp : (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) :
    (matHom _ σ J p⁻¹).1 * adMat F x = (l⁻¹).1 • adMat F x := by
  have := congrArg (fun z => (l⁻¹).1 • ((matHom _ σ J p⁻¹).1 * z)) hp
  simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
    Matrix.mul_smul, smul_smul] at this
  simpa using this.symm

theorem absE_pos (l : (AF F ⊗[F] E)ˣ) : (0 : ℝ) < absE F E l := by
  have h1 : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have : absE F E l ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact_mod_cast pos_iff_ne_zero.2 this

theorem h_pos (hh : IsIwaHtG σ J x L a h) (g : GAd σ J) : 0 < h g := by
  obtain ⟨q, l, hq, k, hk, rfl⟩ := hh.1 g
  rw [hh.2 q l hq k hk]
  exact absE_pos l

theorem h_left (hh : IsIwaHtG σ J x L a h) {p : GAd σ J} {l : (AF F ⊗[F] E)ˣ}
    (hp : (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) (g : GAd σ J) : h (p * g) = absE F E l * h g := by
  obtain ⟨q, l', hq, k, hk, rfl⟩ := hh.1 g
  rw [← mul_assoc, hh.2 _ _ (line_mul hp hq) k hk, hh.2 q l' hq k hk, map_mul, NNReal.coe_mul]

theorem h_right (hh : IsIwaHtG σ J x L a h) (g : GAd σ J) {m : GAd σ J} (hm : m ∈ levelAll σ J L a) :
    h (g * m) = h g := by
  obtain ⟨q, l, hq, k, hk, rfl⟩ := hh.1 g
  rw [mul_assoc, hh.2 q l hq _ (mul_mem hk hm), hh.2 q l hq k hk]

end Height

theorem div_cpow_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    (((x / y : ℝ)) : ℂ) ^ z = (y : ℂ) ^ (-z) * (x : ℂ) ^ z := by
  rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx.le (inv_nonneg.2 hy.le),
    Complex.ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_ne_zero.symm),
    Complex.cpow_neg, mul_comm]

theorem cpow_bound {x : ℝ} (hx : 0 < x) (z₀ ρ : ℂ) {s : ℂ} (hs : s ∈ Metric.ball z₀ 1) :
    ‖(x : ℂ) ^ (-(s + ρ))‖ ≤ x ^ (‖z₀‖ + 1 + ‖ρ‖) + x ^ (-(‖z₀‖ + 1 + ‖ρ‖)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hd : ‖s - z₀‖ < 1 := by simpa [dist_eq_norm] using hs
  have hn : ‖-(s + ρ)‖ ≤ ‖z₀‖ + 1 + ‖ρ‖ := by
    rw [norm_neg]
    calc ‖s + ρ‖ ≤ ‖s‖ + ‖ρ‖ := norm_add_le _ _
      _ ≤ ‖z₀‖ + 1 + ‖ρ‖ := by
        have h2 : ‖s‖ ≤ ‖z₀‖ + ‖s - z₀‖ := by
          calc ‖s‖ = ‖z₀ + (s - z₀)‖ := by rw [add_sub_cancel]
            _ ≤ _ := norm_add_le _ _
        linarith
  have h1 : |(-(s + ρ)).re| ≤ ‖z₀‖ + 1 + ‖ρ‖ := (Complex.abs_re_le_norm _).trans hn
  have hA := abs_le.1 h1
  rcases le_or_gt 1 x with h | h
  · exact (Real.rpow_le_rpow_of_exponent_le h hA.2).trans (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge hx h.le hA.1).trans (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))

end GlobalTheory.EisReduce

namespace GlobalTheory.EisReduce
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.SquareIntegrability

theorem eisAtMinusRho_of_core : EisCore → GlobalTheory.ConeSmall.EisAtMinusRho := by
  intro hCore F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' hT K hK
  have hB := hT.base
  have hcm : IsCMExt F E σ := hB.cm
  have hσ : ∀ z : E, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  obtain ⟨m, Xf, Yf, L, a0, c, hW, hA, hcol, hKc⟩ := GlobalTheory.T.stabilizer_finite_index_chain F E σ B (b + 2) b G.V' G₁.V' G.q (b + 2 - G.q) 0
    (b + 1) H hB hT.geo.hV' hC.hH K hK
  have hJt : (1 : E) • G.V'.J.map σ = G.V'.Jᵀ := by
    ext i j
    simp [Matrix.transpose_apply, hT.geo.hV'.herm j i]
  have hND : IsHermND σ ((1 : E) • G.V'.J.map σ) := hJt ▸ GlobalTheory.IwLine.isHermND_transpose hT.geo.hV'
  obtain ⟨h0, hh0⟩ := GlobalTheory.T.iwasawa_height_adapted_lattice F E σ (b + 2) _ m Xf Yf L a0 hcm hB.unram hND hW hA
  have h4 : 4 ≤ b + 2 := by
    have := hT.geo.aBig
    have := hC.eq
    omega
  obtain ⟨Eis0, hSer0, hMer0, hRho0⟩ := hCore F E σ (b + 2) _ m Xf Yf L a0 h0 ⟨hcm, hB.unram, hND, h4, hW, hA, hh0⟩
  rw [hcol] at hh0 hSer0
  obtain ⟨e, he⟩ : ∃ e : UA σ G.V'.J ≃* GAd σ ((1 : E) • G.V'.J.map σ), ∀ g, matHom _ σ ((1 : E) • G.V'.J.map σ) (e g) =
      (g : GL (Fin (b + 2)) (AF F ⊗[F] E)) := ⟨toGAd hσ G.V'.J one_ne_zero, fun g => rfl⟩
  have hht : ∀ g, height σ ((1 : E) • G.V'.J.map σ) (e g) = ht g := fun g => by
    simp only [GlobalTheory.AdelicU.height, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht, he]
  set ρ : ℂ := (((b + 2 : ℕ) : ℂ) - 1) / 2 with hρ
  have hc0 : 0 < h0 c := h_pos hh0 c
  have hval : ∀ g : UA σ G.V'.J, (g : GL (Fin (b + 2)) (AF F ⊗[F] E)) = matHom _ σ ((1 : E) • G.V'.J.map σ) (e g) := fun g => (he g).symm
  have kc : ∀ k ∈ K, ∃ mm ∈ levelAll σ ((1 : E) • G.V'.J.map σ) L a0, e k * c = c * mm := fun k hk => by
    obtain ⟨mm, hmm, hk'⟩ := (hKc k).1 hk
    refine ⟨mm, hmm, matHom_injective _ σ ((1 : E) • G.V'.J.map σ) ?_⟩
    rw [map_mul, map_mul, ← hval, hk']
    group

  refine ⟨fun s g => (h0 c : ℂ) ^ (-(s + ρ)) * Eis0 s (e g * c),
    ⟨fun g => h0 (e g * c) / h0 c, ?hiwa, ?hdec, ?hser⟩, ?hmer, ?hrho⟩
  case hiwa =>
    intro p k l hk hp
    obtain ⟨mm, hmm, hkc⟩ := kc k hk
    show h0 (e (p * k) * c) / h0 c = absE F E l
    rw [map_mul, mul_assoc, hkc, ← mul_assoc, h_right hh0 _ hmm, h_left hh0 ((line_iff e he _ p l).1 hp) c,
      mul_div_assoc, div_self hc0.ne', mul_one]
  case hdec =>
    intro g
    obtain ⟨q, l, hq, mq, hmq, hg⟩ := hh0.1 (e g * c)
    obtain ⟨q₁, l₁, hq₁, m₁, hm₁, hc⟩ := hh0.1 c
    refine ⟨e.symm (q * q₁⁻¹), e.symm (c * (m₁⁻¹ * mq) * c⁻¹), l * l₁⁻¹, ?_, ?_, ?_⟩
    · rw [hKc]
      refine ⟨m₁⁻¹ * mq, mul_mem (inv_mem hm₁) hmq, ?_⟩
      rw [hval, MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv]
    · rw [line_iff e he, MulEquiv.apply_symm_apply]
      exact line_mul hq (line_inv hq₁)
    · apply e.injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      have e1 : q * q₁⁻¹ * (c * (m₁⁻¹ * mq) * c⁻¹) = q * q₁⁻¹ * c * m₁⁻¹ * mq * c⁻¹ := by group
      have e2 : q * q₁⁻¹ * c = q * m₁ := by rw [hc]; group
      rw [e1, e2, mul_inv_cancel_right, ← hg]
      group
  case hser =>
    intro T hTsub hTt s hs g
    have memP : ∀ u ∈ ratU σ G.V'.J, e u ∈ ratPts σ ((1 : E) • G.V'.J.map σ) := fun u hu => by
      obtain ⟨mu, hmu⟩ := Subgroup.mem_subgroupOf.1 hu
      have h2 := (e u).2
      have hmu' : Formalism.UG.bc (inclR (AF F)) mu = matHom _ σ ((1 : E) • G.V'.J.map σ) (e u) := by
        rw [he]
        exact hmu
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨mu, ?_, hmu'⟩)
      exact unitary_of_map_inclR σ (b + 2) _ mu _ hmu'.symm h2
    have memU : ∀ γ : ratPts σ ((1 : E) • G.V'.J.map σ), e.symm γ.1 ∈ ratU σ G.V'.J := fun γ => by
      obtain ⟨u, -, hu2⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
      exact Subgroup.mem_subgroupOf.2 ⟨u, by rw [← he, MulEquiv.apply_symm_apply]; exact hu2⟩
    set T' : Set (ratPts σ ((1 : E) • G.V'.J.map σ)) := {t | e.symm t.1 ∈ T} with hT'
    have hTt' : ∀ γ : ratPts σ ((1 : E) • G.V'.J.map σ), ∃! t, t ∈ T' ∧ ∃ l : (AF F ⊗[F] E)ˣ,
        (matHom _ σ ((1 : E) • G.V'.J.map σ) (γ * t⁻¹ : ratPts σ ((1 : E) • G.V'.J.map σ)).1).1 * adMat F (Matrix.of fun i (_ : Fin 1) => H.x i) =
          l.1 • adMat F (Matrix.of fun i (_ : Fin 1) => H.x i) := by
      intro γ
      obtain ⟨t, ⟨htT, l, hl⟩, huniq⟩ := hTt (e.symm γ.1) (memU γ)
      refine ⟨⟨e t, memP t (hTsub htT)⟩, ⟨by simpa [T'] using htT, l, ?_⟩, ?_⟩
      · rw [line_iff e he] at hl
        simpa [map_mul, map_inv] using hl
      · rintro t' ⟨ht'T, l', hl'⟩
        have := huniq (e.symm t'.1) ⟨ht'T, l', by rw [line_iff e he]; simpa [map_mul, map_inv] using hl'⟩
        apply Subtype.ext
        simp [← this]
    let eqv : T ≃ T' :=
      { toFun := fun u => ⟨⟨e u.1, memP _ (hTsub u.2)⟩, by simp [T', u.2]⟩
        invFun := fun t => ⟨e.symm t.1.1, t.2⟩
        left_inv := fun u => by simp
        right_inv := fun t => by simp }
    have H1 := (hSer0 T' hTt' s hs (e g * c)).mul_left ((h0 c : ℂ) ^ (-(s + ρ)))
    rw [← eqv.hasSum_iff] at H1
    refine H1.congr_fun fun u => ?_
    show ((h0 (e (u.1 * g) * c) / h0 c : ℝ) : ℂ) ^ _ = _
    rw [map_mul, mul_assoc, div_cpow_pos (h_pos hh0 _) hc0]
    rfl
  case hmer =>
    intro s₀
    obtain ⟨k, U, Hol0, C0, N0, hU, hHol, hdiff, hbd⟩ := hMer0 s₀
    refine ⟨k, U ∩ Metric.ball s₀ 1, fun s g => (h0 c : ℂ) ^ (-(s + ρ)) * Hol0 s (e g * c),
      (h0 c ^ (‖s₀‖ + 1 + ‖ρ‖) + h0 c ^ (-(‖s₀‖ + 1 + ‖ρ‖))) * max C0 0 * (height σ ((1 : E) • G.V'.J.map σ) c : ℝ) ^ N0, N0,
      Filter.inter_mem hU (Metric.ball_mem_nhds _ one_pos), ?_, ?_, ?_⟩
    · intro s hs hne g
      simp only
      rw [hHol s hs.1 hne]
      ring
    · intro g s hs
      refine DifferentiableAt.differentiableWithinAt ?_ |>.mul ((hdiff (e g * c)).mono Set.inter_subset_left s hs)
      exact DifferentiableAt.const_cpow ((differentiableAt_id.add_const ρ).neg) (Or.inl (by exact_mod_cast hc0.ne'))
    · intro s hs g
      have hb := cpow_bound hc0 s₀ ρ hs.2
      have hH := hbd s hs.1 (e g * c)
      have hm : (height σ ((1 : E) • G.V'.J.map σ) (e g * c) : ℝ) ≤ (ht g : ℝ) * height σ ((1 : E) • G.V'.J.map σ) c := by
        have := height_mul_le σ ((1 : E) • G.V'.J.map σ) (e g) c
        rw [hht] at this
        exact_mod_cast this
      simp only
      rw [norm_mul]
      calc ‖(h0 c : ℂ) ^ (-(s + ρ))‖ * ‖Hol0 s (e g * c)‖
          ≤ (h0 c ^ (‖s₀‖ + 1 + ‖ρ‖) + h0 c ^ (-(‖s₀‖ + 1 + ‖ρ‖))) *
            (max C0 0 * ((ht g : ℝ) * height σ ((1 : E) • G.V'.J.map σ) c) ^ N0) := by
            refine mul_le_mul hb (hH.trans ?_) (norm_nonneg _) (by positivity)
            exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by positivity) hm _) (by positivity)
              (le_max_right _ _)
        _ = _ := by rw [mul_pow]; ring
  case hrho =>
    obtain ⟨U, hU, C0, N0, hU0⟩ := hRho0
    refine ⟨U ∩ Metric.ball (-ρ) 1, Filter.inter_mem hU (Metric.ball_mem_nhds _ one_pos),
      (h0 c ^ (‖-ρ‖ + 1 + ‖ρ‖) + h0 c ^ (-(‖-ρ‖ + 1 + ‖ρ‖))) * max C0 0 * (height σ ((1 : E) • G.V'.J.map σ) c : ℝ) ^ N0, N0,
      fun g => ⟨?_, ?_, ?_⟩⟩
    · intro s hs
      refine DifferentiableAt.differentiableWithinAt ?_ |>.mul (((hU0 (e g * c)).1).mono Set.inter_subset_left s hs)
      exact DifferentiableAt.const_cpow ((differentiableAt_id.add_const ρ).neg) (Or.inl (by exact_mod_cast hc0.ne'))
    · intro s hs
      have hb := cpow_bound hc0 (-ρ) ρ hs.2
      have hH := (hU0 (e g * c)).2.1 s hs.1
      have hm : (height σ ((1 : E) • G.V'.J.map σ) (e g * c) : ℝ) ≤ (ht g : ℝ) * height σ ((1 : E) • G.V'.J.map σ) c := by
        have := height_mul_le σ ((1 : E) • G.V'.J.map σ) (e g) c
        rw [hht] at this
        exact_mod_cast this
      rw [norm_mul]
      calc ‖(h0 c : ℂ) ^ (-(s + ρ))‖ * ‖Eis0 s (e g * c)‖
          ≤ (h0 c ^ (‖-ρ‖ + 1 + ‖ρ‖) + h0 c ^ (-(‖-ρ‖ + 1 + ‖ρ‖))) *
            (max C0 0 * ((ht g : ℝ) * height σ ((1 : E) • G.V'.J.map σ) c) ^ N0) := by
            refine mul_le_mul hb (hH.trans ?_) (norm_nonneg _) (by positivity)
            exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by positivity) hm _) (by positivity)
              (le_max_right _ _)
        _ = _ := by rw [mul_pow]; ring
    · show (h0 c : ℂ) ^ (-(-ρ + ρ)) * Eis0 (-ρ) (e g * c) = 1
      rw [(hU0 (e g * c)).2.2, neg_add_cancel, neg_zero, Complex.cpow_zero, mul_one]

end GlobalTheory.EisReduce

end
