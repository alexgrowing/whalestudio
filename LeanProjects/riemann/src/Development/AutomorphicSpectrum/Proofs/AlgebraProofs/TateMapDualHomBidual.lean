import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvdMulOfGroupLikeVal

noncomputable section

open CategoryTheory TensorProduct GlobalTheory GlobalTheory.PDivGroup WithConv

namespace GlobalTheory.CompanionTheory.Ar.HT.Lagr

section Rank

variable {O : Type} [CommRing O] [IsDomain O]

theorem exists_smul_mem {Q : Type} [AddCommGroup Q] [Module O Q]
    (hQ : Module.rank O Q < Cardinal.aleph0) (P : Submodule O Q)
    (h : Module.finrank O Q ≤ Module.finrank O P) (y : Q) : ∃ a : O, a ≠ 0 ∧ a • y ∈ P := by
  have hP : Module.rank O P < Cardinal.aleph0 := (Submodule.rank_le P).trans_lt hQ
  have h1 := HasRankNullity.rank_quotient_add_rank P
  have h2 : Module.rank O P = Module.rank O Q := by
    refine le_antisymm (Submodule.rank_le P) ?_
    rw [← Cardinal.cast_toNat_of_lt_aleph0 hQ, ← Cardinal.cast_toNat_of_lt_aleph0 hP]
    exact Nat.cast_le.2 h
  have h3 : Module.rank O (Q ⧸ P) = 0 := by
    refine Cardinal.eq_of_add_eq_add_right (b := Module.rank O P) ?_ hP
    rw [h1, h2, zero_add]
  obtain ⟨a, ha, hy⟩ := rank_eq_zero_iff.1 h3 (Submodule.Quotient.mk y)
  exact ⟨a, ha, (Submodule.Quotient.mk_eq_zero P).1 (by rw [Submodule.Quotient.mk_smul]; exact hy)⟩

variable {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]

theorem finrank_range_add_ker {M' : Type} [AddCommGroup M'] [Module O M'] (f : M →ₗ[O] M') :
    Module.finrank O (LinearMap.range f) + Module.finrank O (LinearMap.ker f) =
      Module.finrank O M := by
  have h1 : Module.rank O (LinearMap.range f) < Cardinal.aleph0 := Module.rank_lt_aleph0 O _
  have h2 : Module.rank O (LinearMap.ker f) < Cardinal.aleph0 :=
    (Submodule.rank_le _).trans_lt (Module.rank_lt_aleph0 O M)
  have h3 := congrArg Cardinal.toNat (LinearMap.rank_range_add_rank_ker f)
  rwa [Cardinal.toNat_add h1 h2] at h3

theorem finrank_le_add (B : M →ₗ[O] M →ₗ[O] O) (W N : Submodule O M)
    (hN : ∀ x, x ∈ N ↔ ∀ y ∈ W, B x y = 0) :
    Module.finrank O M ≤ Module.finrank O W + Module.finrank O N := by
  have hWr : Module.rank O W < Cardinal.aleph0 :=
    (Submodule.rank_le W).trans_lt (Module.rank_lt_aleph0 O M)
  obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_finrank (R := O) (M := W) le_rfl
  let S : Submodule O W := Submodule.span O (Set.range w)
  have hS : Module.finrank O W ≤ Module.finrank O S := by
    rw [finrank_span_eq_card hw, Fintype.card_fin]
  let Φ : M →ₗ[O] (Fin (Module.finrank O W) → O) := LinearMap.pi fun j => B.flip (w j : M)
  have hker : LinearMap.ker Φ = N := by
    ext x
    rw [hN, LinearMap.mem_ker]
    constructor
    · intro hx y hy
      obtain ⟨a, ha, hay⟩ := exists_smul_mem hWr S hS ⟨y, hy⟩
      have h0 : ∀ s ∈ S, B x (s : M) = 0 := fun s hs => by
        induction hs using Submodule.span_induction with
        | mem s hs =>
          obtain ⟨j, rfl⟩ := hs
          exact congrFun hx j
        | zero => simp
        | add s t _ _ hs ht => simp [hs, ht]
        | smul c s _ hs => simp [hs]
      have h1 := h0 _ hay
      simp only [Submodule.coe_smul, map_smul, smul_eq_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left ha
    · intro hx
      exact funext fun j => hx _ (w j).2
  have h1 := finrank_range_add_ker Φ
  have h2 : Module.finrank O (LinearMap.range Φ) ≤ Module.finrank O W := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    simpa using this
  rw [hker] at h1
  omega

theorem le_of_finrank (B : M →ₗ[O] M →ₗ[O] O) (W N : Submodule O M)
    (hN : ∀ x, x ∈ N ↔ ∀ y ∈ W, B x y = 0) (hNW : N ≤ W)
    (hr : 2 * Module.finrank O W ≤ Module.finrank O M) : W ≤ N := by
  have hWr : Module.rank O W < Cardinal.aleph0 :=
    (Submodule.rank_le W).trans_lt (Module.rank_lt_aleph0 O M)
  have h1 := finrank_le_add B W N hN
  let P : Submodule O W := N.comap W.subtype
  have hP : Module.finrank O W ≤ Module.finrank O P := by
    have : Module.finrank O P = Module.finrank O N :=
      (Submodule.comapSubtypeEquivOfLe hNW).finrank_eq
    omega
  intro x hx
  obtain ⟨a, ha, hax⟩ := exists_smul_mem hWr P hP ⟨x, hx⟩
  rw [hN]
  intro y hy
  have h2 : a • x ∈ N := hax
  have h3 := (hN _).1 h2 y hy
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h3
  exact (mul_eq_zero.1 h3).resolve_left ha

end Rank

section Tate

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

theorem charElem_bidual (G : PDivGroup p O) (t : G.Tate) (n : ℕ) :
    charElem (G := G.dual) (tateMap G G.dual.dual O G.bidual.hom t) n =
      toConv (t.pt n).toLinearMap :=
  (charHom_app_muT _ n).symm.trans (dualChar_app_muT t n)

theorem pairing_dual_bidual (G : PDivGroup p O) (t : G.Tate) (χ : G.dual.Tate) :
    pairing G.dual O χ (tateMap G G.dual.dual O G.bidual.hom t) = pairing G O t χ :=
  muRoot_ext fun n => by
    rw [muRoot_pairing, muRoot_pairing, charElem_bidual]
    exact (apply_charElem χ n _).symm

theorem algebraMap_injective [IsDomain O] [Algebra ℤ_[p] O] (hp : (p : O) ≠ 0) :
    Function.Injective (algebraMap ℤ_[p] O) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  have h2 := congrArg (algebraMap ℤ_[p] O) (PadicInt.unitCoeff_spec h)
  rw [ha, map_mul, map_pow, map_natCast] at h2
  rcases mul_eq_zero.1 h2.symm with h3 | h3
  · exact ((PadicInt.unitCoeff h).isUnit.map (algebraMap ℤ_[p] O)).ne_zero h3
  · exact pow_ne_zero _ hp h3

theorem tateMap_dualHom_bidual (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C]
    [IsAlgClosed C] [CharZero C] [IsDomain O] [Algebra ℤ_[p] O] (hp : (p : O) ≠ 0)
    (G : PDivGroup p O) (lam : G ⟶ G.dual) (μ : (mu p O).Tate)
    (B : O ⊗[ℤ_[p]] G.Tate →ₗ[O] O ⊗[ℤ_[p]] G.Tate →ₗ[O] O)
    (hB : ∀ x y : G.Tate, ∃ a : ℤ_[p], pairing G O y (tateMap G G.dual O lam x) = a • μ ∧
      B (1 ⊗ₜ x) (1 ⊗ₜ y) = algebraMap ℤ_[p] O a)
    (hskew : ∀ x y, B x y = - B y x) (t : G.Tate) :
    tateMap _ _ O (dualHom G G.dual lam) (tateMap G G.dual.dual O G.bidual.hom t) =
      - tateMap G G.dual O lam t := by
  refine (G.pairing_flip_bijective C).1 (LinearMap.ext fun y => ?_)
  change pairing G O y _ = pairing G O y _
  rw [← pairing_tateMap, pairing_dual_bidual, map_neg]
  obtain ⟨a, ha, hb⟩ := hB y t
  obtain ⟨a', ha', hb'⟩ := hB t y
  have h : a = - a' := algebraMap_injective hp (by rw [map_neg, ← hb, ← hb', hskew])
  rw [ha, ha', h, neg_smul]

end Tate

end GlobalTheory.CompanionTheory.Ar.HT.Lagr

namespace GlobalTheory.CompanionTheory.Ar.HT

open AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField GlobalTheory.CompanionTheory.Ar
  GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi Lagr

theorem dlog_lagrangian : FarguesHodgeTate → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) [Algebra ℤ_[p] O] (G : PDivGroup p O) [Module.Free O G.omega] [Module.Finite O G.omega] (lam : G ⟶ G.dual) (ζ : ℕ → O) (h0 : ζ 0 = 1) (h : ∀ n, ζ (n + 1) ^ p = ζ n) (B : O ⊗[ℤ_[p]] G.Tate →ₗ[O] O ⊗[ℤ_[p]] G.Tate →ₗ[O] O) (κ : O), ζ 1 ≠ 1 → IsHTConst v p κ → Function.Bijective (tateMap G G.dual O lam) → 2 * Module.finrank O G.omega = G.height → (∀ x y : G.Tate, ∃ a : ℤ_[p], pairing G O y (tateMap G G.dual O lam x) = a • muTate O ζ h0 h ∧ B (1 ⊗ₜ x) (1 ⊗ₜ y) = algebraMap ℤ_[p] O a) → (∀ x, B x x = 0) → (∀ w : G.omega, κ • w ∈ LinearMap.range (dlogLinear G ∘ₗ (tateMap G G.dual O lam).baseChange O)) ∧ ∀ x, (dlogLinear G ∘ₗ (tateMap G G.dual O lam).baseChange O) x = 0 ↔ ∀ y, (dlogLinear G ∘ₗ (tateMap G G.dual O lam).baseChange O) y = 0 → B x y = 0 := by
  intro hF p _ C _ _ _ v O _ _ _ hv hp hO _ G _ _ lam ζ h0 h B κ hζ hκ hbij hdim hB halt
  have hpp : p.Prime := Fact.out
  have : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2
    ⟨hv.hom_inj, fun hx => hv.exists_of_le_one (hv.mem_of_integral hx)⟩
  have := G.finite_tate C
  have := G.free_tate C
  have hp0 : (p : O) ≠ 0 := fun h => by
    have h5 : algebraMap O C (p : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h5
    exact Nat.cast_ne_zero.2 hpp.ne_zero h5
  have hκ0 : κ ≠ 0 := fun h => hκ.1 (by rw [h, map_zero])
  have hskew : ∀ x y, B x y = - B y x := fun x y => by
    have h1 := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h1
    exact eq_neg_of_add_eq_zero_right h1
  let e : G.Tate ≃ₗ[ℤ_[p]] G.dual.Tate := LinearEquiv.ofBijective _ hbij
  let L : O ⊗[ℤ_[p]] G.Tate ≃ₗ[O] O ⊗[ℤ_[p]] G.dual.Tate := e.baseChange ℤ_[p] O _ _
  have hL : ∀ x, (tateMap G G.dual O lam).baseChange O x = L x := fun _ => rfl
  set f := dlogLinear G ∘ₗ (tateMap G G.dual O lam).baseChange O with hf
  have hfL : ∀ x, f x = dlogLinear G (L x) := fun _ => rfl
  have hcoker : ∀ w : G.omega, κ • w ∈ LinearMap.range f := fun w => by
    obtain ⟨u, hu⟩ := coker_dlog_killed p C v O hv hp hO G κ hκ.2 w
    exact ⟨L.symm u, by rw [hfL, L.apply_symm_apply, hu]⟩
  refine ⟨hcoker, ?_⟩

  let B' : O ⊗[ℤ_[p]] G.Tate →ₗ[O] O ⊗[ℤ_[p]] G.dual.Tate →ₗ[O] O :=
    (B ∘ₗ L.symm.toLinearMap).flip
  have hB' : ∀ (x : G.Tate) (χ : G.dual.Tate), ∃ a : ℤ_[p],
      pairing G O x χ = a • muTate O ζ h0 h ∧ B' (1 ⊗ₜ x) (1 ⊗ₜ χ) = algebraMap ℤ_[p] O a := by
    intro x χ
    obtain ⟨z, rfl⟩ := hbij.2 χ
    obtain ⟨a, ha, hb⟩ := hB z x
    refine ⟨a, ha, ?_⟩
    have h1 : L.symm (1 ⊗ₜ tateMap G G.dual O lam z) = 1 ⊗ₜ z := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    change B (L.symm _) _ = _
    rw [h1, hb]
  have hN : ∀ x, x ∈ LinearMap.ker (hodgeTateLinear G) ↔
      ∀ y ∈ LinearMap.ker f, B x y = 0 := by
    intro x
    rw [LinearMap.mem_ker, (hF p C v O hv hp hO G).2 ζ h0 h hζ B' hB' x]
    constructor
    · intro hx y hy
      have h1 := hx (L y) hy
      have h2 : B y x = 0 := by
        have : B' x (L y) = B y x := by
          change B (L.symm (L y)) x = _
          rw [L.symm_apply_apply]
        rwa [this] at h1
      rw [hskew, h2, neg_zero]
    · intro hx y hy
      have h1 := hx (L.symm y) (by
        rw [LinearMap.mem_ker, hfL, L.apply_symm_apply]
        exact hy)
      change B (L.symm y) x = 0
      rw [hskew, h1, neg_zero]

  have hkey : ∀ x, omegaMap G G.dual lam (hodgeTateLinear G x) = - f x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, neg_add]
    | tmul c t =>
      have h1 : omegaMap G G.dual lam (hodgeTate G t) = - dlog G (tateMap G G.dual O lam t) := by
        rw [hodgeTate_apply, ← dlog_tateMap,
          tateMap_dualHom_bidual C hp0 G lam (muTate O ζ h0 h) B hB hskew, map_neg]
      have h2 : f (c ⊗ₜ t) = c • dlog G (tateMap G G.dual O lam t) := rfl
      rw [hodgeTateLinear_tmul, map_smul, h1, h2, smul_neg]
  have hNW : LinearMap.ker (hodgeTateLinear G) ≤ LinearMap.ker f := fun x hx => by
    have h1 := hkey x
    rw [LinearMap.mem_ker.1 hx, map_zero] at h1
    exact LinearMap.mem_ker.2 (neg_eq_zero.1 h1.symm)

  have hM : Module.finrank O (O ⊗[ℤ_[p]] G.Tate) = G.height := by
    rw [Module.finrank_baseChange, G.finrank_tate C]
  let g : G.omega →ₗ[O] LinearMap.range f :=
    LinearMap.codRestrict _ (κ • LinearMap.id) hcoker
  have hg : Function.Injective g := fun a b hab => by
    have h1 : κ • a = κ • b := congrArg Subtype.val hab
    exact smul_right_injective _ hκ0 h1
  have h1 := LinearMap.finrank_le_finrank_of_injective hg
  have h2 := (finrank_range_add_ker f).trans hM
  have h3 : 2 * Module.finrank O (LinearMap.ker f) ≤ G.height := by
    omega
  have hWN := le_of_finrank B (LinearMap.ker f) _ hN hNW (h3.trans_eq hM.symm)
  intro x
  constructor
  · intro hx y hy
    exact (hN x).1 (hWN hx) y hy
  · intro hx
    exact hNW ((hN x).2 hx)

end GlobalTheory.CompanionTheory.Ar.HT
