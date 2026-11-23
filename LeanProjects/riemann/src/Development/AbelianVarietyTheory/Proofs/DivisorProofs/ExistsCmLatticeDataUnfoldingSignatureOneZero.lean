import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmPointLatticeDataOfAdaptedBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.CMRankOne

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_pure_of_data (Y : FD.Data E r) (x : FD.Frame Y.Ψ r) (hx : x ∈ Y.dom) (lam : Fin r → Fin r → E)
    (ho : ∀ j k' : Fin r, (j : ℕ) < Y.p0 → Y.p0 ≤ (k' : ℕ) → FD.herm Y.Gm (lam j) (lam k') = 0)
    (hsp : ∀ τ : Y.Ψ, Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.col (FD.mat x τ) (Fin.castLE Y.p0_le a)) =
      Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.Data.emb τ.1 (lam (Fin.castLE Y.p0_le a))))
    (a : E) (j : Fin r) (τ : E →+* ℂ) (i : ℕ) :
    ((j : ℕ) < Y.p0 → τ ∈ Y.Ψ → perFr Y x (a • lam j) τ i = 0) ∧
      (Y.p0 ≤ (j : ℕ) → τ ∉ Y.Ψ → i < Y.p0 → perFr Y x (a • lam j) τ i = 0) := by
  refine ⟨fun hj hτ => ?_, fun hj hτ hi => ?_⟩
  · unfold perFr
    rw [dif_pos hτ]
    split_ifs with h
    · refine GlobalTheory.PurePer.inv_mulVec_eq_zero Y.p0_le _ (hx ⟨τ, hτ⟩).1 ?_ _ (by simp)
      rw [hsp ⟨τ, hτ⟩, GlobalTheory.PurePer.emb_smul']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    · rfl
  · unfold perFr
    rw [dif_neg hτ]
    split_ifs with h' h
    · have hm : FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨Y.p0 - 1 - i, h⟩ ∈
          Submodule.span ℂ (Set.range fun a : Fin Y.p0 =>
            FD.Data.emb (conjEmb τ) (lam (Fin.castLE Y.p0_le a))) := by
        have := hsp ⟨conjEmb τ, h'⟩
        simp only at this
        rw [← this]
        exact Submodule.subset_span ⟨⟨Y.p0 - 1 - i, by omega⟩, rfl⟩
      rw [GlobalTheory.PurePer.emb_smul', FD.hermC_smul_right]
      refine mul_eq_zero_of_right _ ?_
      generalize FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨Y.p0 - 1 - i, h⟩ = w at hm
      induction hm using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨k, rfl⟩ := hw
        rw [FD.hermC_emb, ho _ j (by simpa using k.isLt) hj, map_zero]
      | zero => exact FD.hermC_zero_left _ _ _
      | add a b _ _ ha hb => rw [FD.hermC_add_left, ha, hb, add_zero]
      | smul c a _ ha => rw [FD.hermC_smul_left, ha, mul_zero]
    · rfl
    · rfl

theorem exists_cmLat_rankOne (H : Host E) {p q : ℕ} (Y : FD.Data E r) (x₀ : Y.dom)
    (hr : 0 < r) (hrk : r = p + q) (hp0 : Y.p0 = q) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0)
    (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)
    (φ : D.La ≃ₗ[𝓞 E] Y.Λ)
    (isom : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-Y.ξ0 * FD.herm Y.Gm (φ a : Fin r → E) (φ b)))
    (ix : Fin g → ℕ) (hix : ∀ j, ty j (H.rt : E) ≠ H.rt0 → ix j < q)
    (pm : ∀ a j, Pe a j = perFr Y x₀.1 (φ a : Fin r → E) (ty j) (ix j))
    (D₁ : Datum H) (hp1 : D₁.p = 1) (hq1 : D₁.q = 0)
    (lam : Fin r → Fin r → E) (hL : ∀ j, lam j ∈ Y.Λ) (hli : LinearIndependent E lam)
    (ho : ∀ j k' : Fin r, (j : ℕ) < Y.p0 → Y.p0 ≤ (k' : ℕ) → FD.herm Y.Gm (lam j) (lam k') = 0)
    (hsp : ∀ τ : Y.Ψ, Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.col (FD.mat x₀.1 τ) (Fin.castLE Y.p0_le a)) =
      Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.Data.emb τ.1 (lam (Fin.castLE Y.p0_le a)))) :
    Nonempty (CMLat hP p q) := by
  classical
  have hpure := perFr_pure_of_data Y x₀.1 x₀.2 lam ho hsp
  obtain ⟨G1, io, hioinj, -, -, hG1det, hEF1⟩ :=
    GlobalTheory.exists_herm_coord_of_datum E H D₁ Y.ξ0 Y.ξ0_im Y.ξ0_ne 1 (by omega)
  let lv : D₁.La →ₗ[𝓞 E] E := (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin 1 => E) 0) ∘ₗ io
  have hlv : ∀ x, lv x = io x 0 := fun x => rfl
  have hG0 : G1 0 0 ≠ 0 := by simpa [Matrix.det_unique] using hG1det
  have hform1 : ∀ x y, ((D₁.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (Y.ξ0 * G1 0 0 * lv x * FD.cc (lv y)) := by
    intro x y
    rw [hEF1]
    congr 1
    simp [FD.herm, hlv]
    ring
  have h1ne : (1 : Submodule (𝓞 E) E) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨1, Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero⟩

  obtain ⟨S, hS⟩ := D₁.fin.fg_top
  obtain ⟨N₀, hN₀, hc₀⟩ := GlobalTheory.LamT.CMBasis.exists_nsmul_mem (1 : Submodule (𝓞 E) E) h1ne (fun s : S => lv s)
  let lv0 : D₁.La →ₗ[𝓞 E] E := (N₀ : 𝓞 E) • lv
  have hlv0 : ∀ x, lv0 x = (N₀ : E) * lv x := fun x => by
    simp [lv0, Algebra.smul_def]
  have hlv01 : ∀ x, lv0 x ∈ (1 : Submodule (𝓞 E) E) := by
    have : (⊤ : Submodule (𝓞 E) D₁.La) ≤ (1 : Submodule (𝓞 E) E).comap lv0 := by
      rw [← hS, Submodule.span_le]
      intro s hs
      change lv0 s ∈ (1 : Submodule (𝓞 E) E)
      rw [hlv0]
      exact hc₀ ⟨s, hs⟩
    exact fun x => this Submodule.mem_top

  obtain ⟨M, hM, hcM⟩ := GlobalTheory.LamT.CMBasis.exists_nsmul_mem (1 : Submodule (𝓞 E) E) h1ne
    (fun i : Fin r => (N₀ : E) ^ 2 * FD.herm Y.Gm (lam i) (lam i) / G1 0 0)
  choose t ht using fun i => Submodule.mem_one.1 (hcM i)
  let lv' : D₁.La →ₗ[𝓞 E] E := (M : 𝓞 E) • lv0
  have hlv' : ∀ x, lv' x = ((N₀ * M : ℕ) : E) * lv x := fun x => by
    simp only [lv', LinearMap.smul_apply, Algebra.smul_def, hlv0]
    push_cast
    ring
  have hlv'1 : ∀ x, lv' x ∈ (1 : Submodule (𝓞 E) E) := fun x =>
    Submodule.smul_mem _ (M : 𝓞 E) (hlv01 x)
  have hmem : ∀ x j, lv' x • lam j ∈ Y.Λ := fun x j => by
    obtain ⟨u, hu⟩ := Submodule.mem_one.1 (hlv'1 x)
    rw [← hu, algebraMap_smul]
    exact Y.Λ.smul_mem u (hL j)
  let m : Fin r → D₁.La →ₗ[𝓞 E] Y.Λ := fun j =>
    { toFun := fun a => ⟨_, hmem a j⟩
      map_add' := fun a b => Subtype.ext (by simp [add_smul])
      map_smul' := fun c a => Subtype.ext (by simp [smul_assoc]) }
  let Dp : Bool → Datum H := fun b => match b with
    | true => D₁
    | false => oppDatum D₁
  let e : ∀ b, (Dp b).La ≃ₗ[𝓞 E] D₁.La := fun b => match b with
    | true => LinearEquiv.refl _ _
    | false => LinearEquiv.refl _ _
  let σ : Fin p ⊕ Fin q ≃ Fin r := (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))
  have hσl : ∀ j, q ≤ (σ (.inl j) : ℕ) := fun j => by simp [σ]
  have hσr : ∀ j, (σ (.inr j) : ℕ) < q := fun j => by simp [σ]
  let f : ∀ j : Fin p ⊕ Fin q, (Dp j.isLeft).La →ₗ[𝓞 E] D.La := fun j =>
    φ.symm.toLinearMap ∘ₗ m (σ j) ∘ₗ (e _).toLinearMap
  have hf : ∀ j a, (φ (f j a) : Fin r → E) = lv' (e _ a) • lam (σ j) := fun j a => by
    simp [f, m]
  let hh : Fin p ⊕ Fin q → 𝓞 E :=
    Sum.elim (fun j => -((M : 𝓞 E) * t (σ (.inl j)))) (fun j => (M : 𝓞 E) * t (σ (.inr j)))
  have hhl : ∀ j, ((hh (.inl j) : 𝓞 E) : E) =
      -(((N₀ * M : ℕ) : E) ^ 2 * FD.herm Y.Gm (lam (σ (.inl j))) (lam (σ (.inl j))) / G1 0 0) := by
    intro j
    show ((-((M : 𝓞 E) * t (σ (.inl j))) : 𝓞 E) : E) = _
    rw [RingOfIntegers.coe_eq_algebraMap, map_neg, map_mul, ht, map_natCast]
    push_cast
    ring
  have hhr : ∀ j, ((hh (.inr j) : 𝓞 E) : E) =
      ((N₀ * M : ℕ) : E) ^ 2 * FD.herm Y.Gm (lam (σ (.inr j))) (lam (σ (.inr j))) / G1 0 0 := by
    intro j
    show ((((M : 𝓞 E) * t (σ (.inr j))) : 𝓞 E) : E) = _
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul, ht, map_natCast]
    push_cast
    ring
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := fun τ => by
    refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
    rw [← map_pow, HostModel.coe_sq_eq_neg H.rt_sq, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  have h3 : ∀ (a b : E) (u : Fin r → E), FD.herm Y.Gm (a • u) (b • u) = a * FD.cc b * FD.herm Y.Gm u u :=
    fun a b u => by
      simp only [FD.herm, FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hccN : ∀ n : ℕ, FD.cc (n : E) = n := fun n => by simp [FD.cc]
  have hlvs : ∀ (c : 𝓞 E) x, lv (c • x) = (c : E) * lv x := fun c x => by
    rw [map_smul, Algebra.smul_def]
  refine ⟨⟨Dp, ⟨hp1, hq1⟩, ⟨hq1, hp1⟩, f, ?_, hh, ?_, ?_⟩⟩
  · rintro (j | j) a k hk
    · rw [pm, hf]
      have hk' : ty k (H.rt : E) ≠ H.rt0 := by simpa using hk
      exact (hpure _ _ _ _).2 (hp0 ▸ hσl j) (fun h => hk' ((hΨ _).1 h)) (hp0 ▸ hix k hk')
    · rw [pm, hf]
      have hk' : ty k (H.rt : E) ≠ -H.rt0 := by simpa using hk
      exact (hpure _ _ _ _).1 (hp0 ▸ hσr j) ((hΨ _).2 ((hsq _).resolve_right hk'))
  · rintro (j | j) a b
    · apply Int.cast_injective (α := ℚ)
      rw [isom, hf, hf]
      refine Eq.trans ?_ (hform1 (hh (.inl j) • a) b).symm
      erw [hlvs]
      congr 1
      change -Y.ξ0 * FD.herm Y.Gm (lv' a • lam (σ (.inl j))) (lv' b • lam (σ (.inl j))) = _
      rw [h3]
      erw [hlv' a, hlv' b]
      rw [hhl]
      simp only [FD.cc, map_mul, map_natCast]
      field_simp
    · apply Int.cast_injective (α := ℚ)
      rw [isom, hf, hf]
      refine Eq.trans ?_ (congrArg (fun z : ℚ => -z) (hform1 (hh (.inr j) • a) b)).symm |>.trans (by push_cast; rfl)
      erw [hlvs]
      rw [← map_neg]
      congr 1
      change -Y.ξ0 * FD.herm Y.Gm (lv' a • lam (σ (.inr j))) (lv' b • lam (σ (.inr j))) = _
      rw [h3]
      erw [hlv' a, hlv' b]
      rw [hhr]
      simp only [FD.cc, map_mul, map_natCast]
      field_simp
  · haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
    have hB : ∀ j, B j = lam j := fun j => by simp [B]
    let Nm : Submodule (𝓞 E) D.La := LinearMap.range (∑ j, f j ∘ₗ LinearMap.proj j)
    have hN : ∀ a, a ∈ Nm ↔ ∃ x : ∀ j : Fin p ⊕ Fin q, (Dp j.isLeft).La, a = ∑ j, f j (x j) := fun a => by
      simp only [Nm, LinearMap.mem_range, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      exact exists_congr fun _ => eq_comm
    have hnt : Nontrivial D₁.La :=
      Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D₁.rank, hp1, hq1]; exact one_pos)
    obtain ⟨a₀, ha₀⟩ := exists_ne (0 : D₁.La)
    have hR : LinearMap.range lv' ≠ ⊥ := by
      refine (Submodule.ne_bot_iff _).2 ⟨lv' a₀, ⟨a₀, rfl⟩, ?_⟩
      rw [hlv']
      refine mul_ne_zero (by exact_mod_cast (Nat.mul_pos hN₀ hM).ne') fun h0 => ha₀ (hioinj ?_)
      funext i
      rw [Subsingleton.elim i 0, map_zero]
      exact h0
    obtain ⟨S', hS'⟩ := D.fin.fg_top
    obtain ⟨n, hn, hc⟩ := GlobalTheory.LamT.CMBasis.exists_nsmul_mem (LinearMap.range lv') hR
      (fun i : S' × Fin r => B.repr (φ i.1 : Fin r → E) i.2)
    choose y hy using fun i : S' × Fin r => LinearMap.mem_range.1 (hc i)
    refine ⟨n, hn, fun a => (hN _).1 ?_⟩
    have : (⊤ : Submodule (𝓞 E) D.La) ≤ Nm.comap (n • LinearMap.id) := by
      rw [← hS', Submodule.span_le]
      intro a ha
      refine (hN _).2 ⟨fun j => (e _).symm (y (⟨a, ha⟩, σ j)), φ.injective (Subtype.ext ?_)⟩
      rw [map_sum, AddSubmonoidClass.coe_finsetSum]
      simp only [hf, LinearEquiv.apply_symm_apply, hy]
      rw [Equiv.sum_comp σ (fun j => ((n : E) * B.repr (φ a : Fin r → E) j) • lam j)]
      simp only [mul_smul, ← Finset.smul_sum, ← hB, B.sum_repr]
      simp [Nat.cast_smul_eq_nsmul]
    exact this Submodule.mem_top

theorem exists_cmLat_unfAt_rankOne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (r : ℕ) (U : Formalism.L2.Pj.Unf Xo c c.F.val.toRingHom r), Formalism.L2.Pj.IsUnf U → 0 < r → ∀ (D₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), D₁.p = 1 → D₁.q = 0 → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt U k x₀) (lam : Fin r → Fin r → E), (∀ j, lam j ∈ (U.X k).Λ) → LinearIndependent E lam → (∀ j k' : Fin r, (j : ℕ) < (U.X k).p0 → (U.X k).p0 ≤ (k' : ℕ) → ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam k') = 0) → (∀ j : Fin r, (j : ℕ) < (U.X k).p0 → ∀ τ : (U.X k).Ψ, 0 < (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam j))).re) → (∀ j : Fin r, (U.X k).p0 ≤ (j : ℕ) → ∀ τ : (U.X k).Ψ, (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam j))).re < 0) → (∀ τ : (U.X k).Ψ, Submodule.span ℂ (Set.range fun a : Fin (U.X k).p0 => ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x₀.1 τ) (Fin.castLE (U.X k).p0_le a)) = Submodule.span ℂ (Set.range fun a : Fin (U.X k).p0 => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (lam (Fin.castLE (U.X k).p0_le a)))) → Nonempty (GlobalTheory.CM.CMLat W.per Dw.p Dw.q) := by
  intro E _ _ _ H Dw l Xo c r U hU hr D₁ hp1 hq1 k x₀ W lam hL hli ho _ _ hsp
  obtain ⟨h1, h2, -⟩ := hU
  refine exists_cmLat_rankOne H (U.X k) x₀ hr h1 (h2 k).1 (h2 k).2 _ W.per (W.φ k) (W.isom k)
    (fun j => (W.e j).2) (fun j hj => ?_) W.pm_eq D₁ hp1 hq1 lam hL hli ho hsp
  exact (W.e j).2.2.trans_eq (if_neg hj)

end GlobalTheory.LamT.CMRankOne
