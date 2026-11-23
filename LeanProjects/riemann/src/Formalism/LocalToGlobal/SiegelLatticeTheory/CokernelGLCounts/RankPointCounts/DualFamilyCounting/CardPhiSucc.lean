import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscOnto

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.LocalizedFibreSets

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

theorem starO_ι (a : 𝓞 F) : star (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap (𝓞 F) (𝓞 K) a := by
  apply RingOfIntegers.ext
  change star ((algebraMap (𝓞 F) (𝓞 K) a : 𝓞 K) : K) = ((algebraMap (𝓞 F) (𝓞 K) a : 𝓞 K) : K)
  have h1 : ((algebraMap (𝓞 F) (𝓞 K) a : 𝓞 K) : K) = algebraMap F K (a : F) := by
    first
    | rfl
    | exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K a).symm.trans
        (IsScalarTower.algebraMap_apply (𝓞 F) F K a)
  rw [h1]
  exact ((Fact.out : IsFixF K F) _).2 ⟨_, rfl⟩

theorem diagQ_herm (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    (diagQ K 𝔭 k a)ᴴ = diagQ K 𝔭 k a := by
  unfold diagQ
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  rw [Pi.star_apply, star_mk, starO_ι]

theorem phiQ_herm (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) : (phiQ K 𝔭 k a Y)ᴴ = phiQ K 𝔭 k a Y := by
  unfold phiQ
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, diagQ_herm]
  simp only [Matrix.mul_assoc]
  abel

theorem map_diagQ (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    (diagQ K 𝔭 (k + 1) a).map (piQ K 𝔭 k) = diagQ K 𝔭 k a := by
  unfold diagQ
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1

theorem map_phiQ (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1))) :
    (phiQ K 𝔭 (k + 1) a Y).map (piQ K 𝔭 k) = phiQ K 𝔭 k a (Y.map (piQ K 𝔭 k)) := by
  have hs : Function.Semiconj (piQ K 𝔭 k) star star := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    unfold piQ
    rw [star_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, star_mk]
  have hd := map_diagQ (K := K) 𝔭 k a
  unfold phiQ
  rw [Matrix.map_add (piQ K 𝔭 k) (map_add (piQ K 𝔭 k)), Matrix.map_add (piQ K 𝔭 k) (map_add (piQ K 𝔭 k)),
    Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map _ hs, hd]

theorem card_phi_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (a : Fin m → 𝓞 F) {k : ℕ} (hk : 1 ≤ k) (T : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)))
    (hT : Tᴴ = T) (hT0 : ∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))) :
    Nat.card {Y // phiQ K 𝔭 (k + 1) a Y = T} =
      Ideal.absNorm 𝔭 ^ (m * m) * Nat.card {Y // phiQ K 𝔭 k a Y = T.map (piQ K 𝔭 k)} := by
  classical
  haveI := finite_quot (K := K) h𝔭 (k + 1)
  haveI := finite_quot (K := K) h𝔭 k
  haveI : Finite (Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1))) := inferInstanceAs (Finite (Fin m → Fin m → (𝓞 K ⧸ extP K 𝔭 ^ (k + 1))))
  haveI : Finite (Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :=
    inferInstanceAs (Finite (Fin m → Fin m → (𝓞 K ⧸ extP K 𝔭 ^ k)))

  have hJJ : ∀ x ∈ (RingHom.ker (piQ K 𝔭 k)), ∀ y ∈ (RingHom.ker (piQ K 𝔭 k)), x * y = 0 := by
    intro x hx y hy
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [mk_mem_ker_piQ] at hx hy
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have huv : u * v ∈ extP K 𝔭 ^ (k + k) := by rw [pow_add]; exact Ideal.mul_mem_mul hx hy
    exact Ideal.pow_le_pow_right (by omega) huv
  have hPJ : ∀ x ∈ ((extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))), ∀ y ∈ (RingHom.ker (piQ K 𝔭 k)), x * y = 0 := by
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hx
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [mk_mem_ker_piQ] at hy
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_succ']
    exact Ideal.mul_mem_mul hu hy
  have hJP : ∀ x ∈ (RingHom.ker (piQ K 𝔭 k)), x ∈ ((extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))) := by
    intro x hx
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [mk_mem_ker_piQ] at hx
    exact Ideal.mem_map_of_mem _ (Ideal.pow_le_self (by omega) hx)
  have hJs : ∀ x ∈ (RingHom.ker (piQ K 𝔭 k)), star x ∈ (RingHom.ker (piQ K 𝔭 k)) := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    rw [piQ_star, hx, star_zero]
  obtain ⟨θ, e, he⟩ := exists_unit_quot hK h𝔭 (k + 1)
  have hmem : ∀ (C E : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1))), E ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)) → C * E ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)) := by
    intro C E hE i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ (fun l _ => Ideal.mul_mem_left _ _ (hE l j))

  have hfib : ∀ (A B : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1))), (∀ G ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)), A * (B * G) = G) →
      ∀ S ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k)), Nat.card {E : Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)) // A * E.1 + (A * E.1)ᴴ = S} =
        Ideal.absNorm 𝔭 ^ (m * m) := by
    intro A B hAB S hS
    let L : Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)) →+ Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) :=
      (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.trH (Fin m) (RingHom.ker (piQ K 𝔭 k))).comp
        (AddMonoidHom.mk' (fun E => ⟨A * E.1, hmem A E.1 E.2⟩)
          (fun E F => Subtype.ext (by simp [Matrix.mul_add])))
    have hL : ∀ E, L E = A * E.1 + (A * E.1)ᴴ := fun E => rfl
    have hrange : L.range = Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k)) := by
      apply le_antisymm
      · rintro _ ⟨E, rfl⟩
        rw [← Formalism.HermitianLattices.Ext.L3.HermitianSublattices.range_trH hJs he]
        exact ⟨⟨A * E.1, hmem _ _ E.2⟩, rfl⟩
      · intro S' hS'
        rw [← Formalism.HermitianLattices.Ext.L3.HermitianSublattices.range_trH hJs he] at hS'
        obtain ⟨G, rfl⟩ := hS'
        refine ⟨⟨B * G.1, hmem _ _ G.2⟩, ?_⟩
        rw [hL]
        show A * (B * G.1) + (A * (B * G.1))ᴴ = G.1 + G.1ᴴ
        rw [hAB G.1 G.2]
    have hcardE : Nat.card (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k))) = Nat.card L.ker * Nat.card (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k))) := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup L.ker,
        Nat.card_congr (QuotientAddGroup.quotientKerEquivRange L).toEquiv, hrange, mul_comm]
    have hsq := Formalism.HermitianLattices.Ext.L3.HermitianSublattices.card_hermSub_sq (r := Fin m) hJs he
    have hh := Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.card_hermSub (r := Fin m) hK h𝔭 k
    rw [Fintype.card_fin] at hh
    have hpos : 0 < Nat.card (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k))) := Nat.card_pos
    have hker : Nat.card L.ker = Nat.card (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k))) := by
      rw [← hsq, pow_two] at hcardE
      exact (Nat.eq_of_mul_eq_mul_right hpos hcardE).symm
    have hSr : S ∈ L.range := by rw [hrange]; exact hS
    obtain ⟨E0, hE0⟩ := hSr
    rw [← hh, ← hker]
    exact Nat.card_congr
      { toFun := fun E => ⟨E.1 - E0, by
          rw [AddMonoidHom.mem_ker, map_sub, hE0, hL, E.2, sub_self]⟩
        invFun := fun K0 => ⟨K0.1 + E0, by
          rw [← hL, map_add, AddMonoidHom.mem_ker.mp K0.2, hE0, zero_add]⟩
        left_inv := fun E => Subtype.ext (sub_add_cancel _ _)
        right_inv := fun K0 => Subtype.ext (add_sub_cancel_right _ _) }

  let f : {Y // phiQ K 𝔭 (k + 1) a Y = T} → {Y // phiQ K 𝔭 k a Y = T.map (piQ K 𝔭 k)} :=
    fun Y => ⟨Y.1.map (piQ K 𝔭 k), by rw [← map_phiQ, Y.2]⟩
  have hfiber : ∀ y, Nat.card {x // f x = y} = Ideal.absNorm 𝔭 ^ (m * m) := by
    rintro ⟨Y', hY'⟩
    obtain ⟨Y0, hY0⟩ : ∃ Y0 : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)), Y0.map (piQ K 𝔭 k) = Y' :=
      ⟨fun i j => (piQ_surjective (K := K) 𝔭 k (Y' i j)).choose,
        by ext i j; exact (piQ_surjective (K := K) 𝔭 k (Y' i j)).choose_spec⟩
    obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)), A = 1 + Y0ᴴ * diagQ K 𝔭 (k + 1) a := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)), B = 1 + Y0 * diagQ K 𝔭 (k + 1) a := ⟨_, rfl⟩
    have hS : T - phiQ K 𝔭 (k + 1) a Y0 ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k)) := by
      refine ⟨?_, ?_⟩
      · rw [Matrix.conjTranspose_sub, hT, phiQ_herm]
      · intro i j
        rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
        have h1 := congrFun (congrFun (map_phiQ 𝔭 k a Y0) i) j
        rw [Matrix.map_apply] at h1
        rw [h1, hY0, hY', Matrix.map_apply, sub_self]
    have hPhi0 : ∀ i j, phiQ K 𝔭 (k + 1) a Y0 i j ∈ ((extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))) := by
      intro i j
      have e1 : phiQ K 𝔭 (k + 1) a Y0 i j = T i j - (T - phiQ K 𝔭 (k + 1) a Y0) i j := by
        rw [Matrix.sub_apply]; ring
      rw [e1]
      exact Ideal.sub_mem _ (hT0 i j) (hJP _ (hS.2 i j))
    have hAB : A * B = 1 + phiQ K 𝔭 (k + 1) a Y0 * diagQ K 𝔭 (k + 1) a := by
      rw [hA, hB]; unfold phiQ; noncomm_ring
    have hABG : ∀ G ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)), A * (B * G) = G := by
      intro G hG
      have h0 : phiQ K 𝔭 (k + 1) a Y0 * diagQ K 𝔭 (k + 1) a * G = 0 := by
        ext i j
        rw [Matrix.mul_apply, Matrix.zero_apply]
        refine Finset.sum_eq_zero (fun l _ => hPJ _ ?_ _ (hG l j))
        rw [Matrix.mul_apply]
        exact Ideal.sum_mem _ (fun l' _ => Ideal.mul_mem_right _ _ (hPhi0 i l'))
      rw [← Matrix.mul_assoc, hAB, Matrix.add_mul, Matrix.one_mul, h0, add_zero]
    have hEE : ∀ E ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)), Eᴴ * diagQ K 𝔭 (k + 1) a * E = 0 := by
      intro E hE
      ext i j
      rw [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero (fun l _ => hJJ _ ?_ _ (hE l j))
      rw [Matrix.mul_apply]
      refine Ideal.sum_mem _ (fun l' _ => Ideal.mul_mem_right _ _ ?_)
      rw [Matrix.conjTranspose_apply]
      exact hJs _ (hE l' i)
    have hDh : (diagQ K 𝔭 (k + 1) a)ᴴ = diagQ K 𝔭 (k + 1) a := diagQ_herm 𝔭 (k + 1) a
    have hexp : ∀ E ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)), phiQ K 𝔭 (k + 1) a (Y0 + E) =
        phiQ K 𝔭 (k + 1) a Y0 + (A * E + (A * E)ᴴ) := by
      intro E hE
      have h1 : (A * E)ᴴ = Eᴴ * (1 + diagQ K 𝔭 (k + 1) a * Y0) := by
        rw [Matrix.conjTranspose_mul, hA, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
          Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hDh]
      rw [h1, hA]
      unfold phiQ
      rw [Matrix.conjTranspose_add]
      calc _ = Y0 + Y0ᴴ + Y0ᴴ * diagQ K 𝔭 (k + 1) a * Y0 +
            ((1 + Y0ᴴ * diagQ K 𝔭 (k + 1) a) * E + Eᴴ * (1 + diagQ K 𝔭 (k + 1) a * Y0)) + Eᴴ * diagQ K 𝔭 (k + 1) a * E := by noncomm_ring
        _ = _ := by rw [hEE E hE, add_zero]
    have hker0 : ∀ E ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)), E.map (piQ K 𝔭 k) = 0 := by
      intro E hE
      ext i j
      exact hE i j
    rw [← hfib A B hABG _ hS]
    exact Nat.card_congr
      { toFun := fun x => ⟨⟨x.1.1 - Y0, by
            intro i j
            have hx := congrArg Subtype.val x.2
            have hx' := congrFun (congrFun hx i) j
            rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
            have hy := congrFun (congrFun hY0 i) j
            simp only [f, Matrix.map_apply] at hx' hy
            rw [hx', hy, sub_self]⟩, by
            have h2 := hexp (x.1.1 - Y0) (by
              intro i j
              have hx := congrArg Subtype.val x.2
              have hx' := congrFun (congrFun hx i) j
              rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
              have hy := congrFun (congrFun hY0 i) j
              simp only [f, Matrix.map_apply] at hx' hy
              rw [hx', hy, sub_self])
            rw [add_sub_cancel, x.1.2] at h2
            show A * (x.1.1 - Y0) + (A * (x.1.1 - Y0))ᴴ = T - phiQ K 𝔭 (k + 1) a Y0
            exact eq_sub_of_add_eq' h2.symm⟩
        invFun := fun E => ⟨⟨Y0 + E.1.1, by rw [hexp E.1.1 E.1.2, E.2, add_sub_cancel]⟩,
          Subtype.ext (by
            show (Y0 + E.1.1).map (piQ K 𝔭 k) = Y'
            rw [Matrix.map_add _ (map_add _), hY0, hker0 E.1.1 E.1.2, add_zero])⟩
        left_inv := fun x => Subtype.ext (Subtype.ext (add_sub_cancel _ _))
        right_inv := fun E => Subtype.ext (Subtype.ext (add_sub_cancel_left _ _)) }
  haveI : Fintype {Y // phiQ K 𝔭 k a Y = T.map (piQ K 𝔭 k)} := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma,
    Finset.sum_congr rfl (fun y _ => hfiber y), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, smul_eq_mul, mul_comm]

def PhiModP : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
      (Nat.card {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ 1) // phiQ K 𝔭 1 a Y = 0} : ℝ) =
        (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2) * alphaStd K 𝔭 (m - cJof 𝔭 a)

theorem phiCount_of (h1 : PhiModP) : PhiCount := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro T _ hT0
    have hb : (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ 1)) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker, pow_one]
    have hT' : T = 0 := by
      ext i j
      have := hT0 i j
      rw [hb, Ideal.mem_bot] at this
      exact this
    subst hT'
    rw [mul_one]
    exact h1 K F hK 𝔭 h𝔭 m a ha
  | succ k hk ih =>
    intro T hT hT0
    have hs : Function.Semiconj (piQ K 𝔭 k) star star := by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      unfold piQ
      rw [star_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, star_mk]
    rw [card_phi_succ hK h𝔭 a hk T hT hT0]
    push_cast
    rw [ih (T.map (piQ K 𝔭 k)) ?_ ?_]
    · ring
    · rw [← Matrix.conjTranspose_map _ hs, hT]
    · intro i j
      obtain ⟨x, hx, hxT⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hT0 i j)
      rw [Matrix.map_apply, ← hxT]
      unfold piQ
      rw [Ideal.Quotient.factor_mk]
      exact Ideal.mem_map_of_mem _ hx

end Formalism.L2.SG.Pf.LocalizedFibreSets
