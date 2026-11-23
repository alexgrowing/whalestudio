import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.InstLCSL
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.LocalDecomp

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.TwSMInt2

open MomentRationality MomentRationality.Cz.Red

theorem sRed_of (hG : SRedGL) : SRed := by
  intro L _ _ hL N hN
  classical
  obtain ⟨R, M, t, hM, ht, H⟩ := hG L hL N hN
  obtain ⟨S, hS⟩ := units_fin (L := L) N (by omega)
  let G : (↥R) × (↥S) → GL (Fin N) L := fun j =>
    ddGL N (Units.map (algebraMap (𝓞 L) L).toMonoidHom ((j.2 : (𝓞 L)ˣ)⁻¹)) * (j.1 : GL (Fin N) L)
  have hGm : ∀ j (w : InfinitePlace L), ((G j : Matrix (Fin N) (Fin N) L).map w.embedding) =
      dd N (embO w (((j.2 : (𝓞 L)ˣ)⁻¹ : (𝓞 L)ˣ) : 𝓞 L)) *
        ((j.1 : GL (Fin N) L) : Matrix (Fin N) (Fin N) L).map w.embedding := by
    intro j w
    have e : (G j : Matrix (Fin N) (Fin N) L) =
        dd N (algebraMap (𝓞 L) L (((j.2 : (𝓞 L)ˣ)⁻¹ : (𝓞 L)ˣ) : 𝓞 L)) *
          ((j.1 : GL (Fin N) L) : Matrix (Fin N) (Fin N) L) := rfl
    rw [e, Matrix.map_mul, dd_map]
    rfl
  have hGd : ∀ j (w : InfinitePlace L), ((G j : Matrix (Fin N) (Fin N) L).map w.embedding).det ≠ 0 := by
    intro j w
    have h := (RingHom.map_det w.embedding (G j : Matrix (Fin N) (Fin N) L)).symm
    rw [RingHom.mapMatrix_apply] at h
    rw [h]
    exact (_root_.map_ne_zero _).2 (G j).det_ne_zero
  choose z hz0 hz using fun j w => exists_root (N := N) (by omega) (hGd j w)
  let c : (↥R) × (↥S) → Sp L N := fun j w => ⟨z j w • (G j : Matrix (Fin N) (Fin N) L).map w.embedding, by
    rw [det_smul, Fintype.card_fin, hz]⟩
  refine ⟨(↥R) × (↥S), inferInstance, c, Real.exp (4 * Real.log M), 4 * Real.log M - Real.log t,
    fun j => ⟨G j, z j, fun w => rfl⟩, fun x => ?_⟩
  obtain ⟨δ, g, hg, r, hr, hrt, hw⟩ := H (ofS L N x)
  choose b hb hbM hbm k hk hbk using hw
  obtain ⟨v, u0, hu0, hu⟩ := hS (GeneralLinearGroup.det δ)
  have hu' : (δ : Matrix (Fin N) (Fin N) (𝓞 L)).det = (v : 𝓞 L) ^ N * u0 := by
    have := congrArg (fun u : (𝓞 L)ˣ => (u : 𝓞 L)) hu
    simpa using this
  let σ : SpecialLinearGroup (Fin N) (𝓞 L) :=
    ⟨((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L) • (dd N ((u0⁻¹ : (𝓞 L)ˣ) : 𝓞 L) * (δ : Matrix (Fin N) (Fin N) (𝓞 L))), by
      rw [det_smul, Fintype.card_fin, det_mul, det_dd hN, hu']
      calc ((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L) ^ N * (((u0⁻¹ : (𝓞 L)ˣ) : 𝓞 L) * ((v : 𝓞 L) ^ N * u0)) =
          (((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L) * v) ^ N * (((u0⁻¹ : (𝓞 L)ˣ) : 𝓞 L) * u0) := by ring
        _ = 1 := by rw [Units.inv_mul, Units.inv_mul, one_pow, one_mul]⟩
  let γ : Sp L N := fun w => SpecialLinearGroup.map (n := Fin N) (embO w) σ
  let j : (↥R) × (↥S) := (⟨g, hg⟩, ⟨u0, hu0⟩)
  refine ⟨γ, ⟨σ, rfl⟩, j, ?_⟩
  obtain ⟨y, hy⟩ : ∃ y : Sp L N, y = (c j)⁻¹ * (γ * x) := ⟨_, rfl⟩
  rw [← hy]
  have hcy : c j * y = γ * x := by rw [hy, mul_inv_cancel_left]
  have hY : ∀ w, MomentRationality.mt y w = ((z j w)⁻¹ * embO w ((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L)) •
      (b w * diagonal (fun i => ((r i : ℝ) : ℂ)) * k w) := by
    intro w
    refine cancel_left (hGd j w) (hz0 j w) ?_
    have h1 : (z j w • (G j : Matrix (Fin N) (Fin N) L).map w.embedding) * MomentRationality.mt y w =
        (((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L) • (dd N ((u0⁻¹ : (𝓞 L)ˣ) : 𝓞 L) *
          (δ : Matrix (Fin N) (Fin N) (𝓞 L)))).map (embO w) * MomentRationality.mt x w :=
      congrArg (fun a => MomentRationality.mt a w) hcy
    have h2 : (δ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) * MomentRationality.mt x w =
        (g : Matrix (Fin N) (Fin N) L).map w.embedding * b w * diagonal (fun i => ((r i : ℝ) : ℂ)) * k w := hbk w
    have h3 : (((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L) • (dd N ((u0⁻¹ : (𝓞 L)ˣ) : 𝓞 L) *
          (δ : Matrix (Fin N) (Fin N) (𝓞 L)))).map (embO w) = embO w ((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L) •
          (dd N (embO w ((u0⁻¹ : (𝓞 L)ˣ) : 𝓞 L)) * (δ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w)) := by
      rw [← dd_map, ← Matrix.map_mul]
      ext i l
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [h1, h3, Matrix.smul_mul, Matrix.mul_assoc, h2, hGm]
    simp only [Matrix.mul_assoc]
    rfl
  obtain ⟨p, k', s, hssum, hsieg, hpT, hpM, hpm, hpP, hpd, hk'U, hk'd, hdec⟩ :=
    local_decomp hN hM ht hr hrt (fun w => (z j w)⁻¹ * embO w ((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L)) b k hb hbM hbm hk
      (fun w => by rw [← hY w]; exact (y w).2)
  refine ⟨fun w => ⟨p w, hpd w⟩, ⟨hpT, hpM, ?_, hpP⟩, s, hssum, hsieg, fun w => ⟨k' w, hk'd w⟩, hk'U, ?_⟩
  · intro w i
    rw [← Real.exp_neg]
    exact hpm w i
  · funext w
    apply Subtype.ext
    show MomentRationality.mt y w = p w * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) * k' w
    rw [hY w, hdec w]

end PositivityTheory.KB.TwSMInt2

end
