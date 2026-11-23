import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
  GlobalTheory.LieMet GlobalTheory.DRFlag
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono
  le_preimage_comp ext_ev)

namespace GlobalTheory.DRFlag

variable {Z : Scheme.{0}}

theorem exists_ev_eq_pow_mul {U W : Z.Opens} (hU : IsAffineOpen U) (f : Γ(Z, U)) (hW : Z.basicOpen f = W)
    (x : Γ(Z, W)) : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ y : Γ(Z, U), ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Z)
      (h : ⊤ ≤ z ⁻¹ᵁ U) (h' : ⊤ ≤ z ⁻¹ᵁ W), ev z U h y = ev z U h f ^ n * ev z W h' x := by
  subst hW
  obtain ⟨n₀, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen Z U hU f x
  refine ⟨n₀, fun n hn => ⟨f ^ (n - n₀) * y, fun S _ z h h' => ?_⟩⟩
  have e : resG Z (Z.basicOpen_le f) y = resG Z (Z.basicOpen_le f) f ^ n₀ * x := hy
  have e' := congrArg (ev z _ h') e
  rw [map_mul, map_pow, ev_res z _ h' h, ev_res z _ h' h] at e'
  rw [map_mul, map_pow, e', ← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]

theorem exists_pow_mul_eq_of_ev {U : Z.Opens} (hU : IsAffineOpen U) (f x y : Γ(Z, U))
    (H : ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Z) (h : ⊤ ≤ z ⁻¹ᵁ U), ⊤ ≤ z ⁻¹ᵁ Z.basicOpen f →
      ev z U h x = ev z U h y) : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → f ^ n * x = f ^ n * y := by
  have e : resG Z (Z.basicOpen_le f) (x - y) = 0 := ext_ev fun S _ z hz => by
    have h := le_preimage_mono (Z.basicOpen_le f) hz
    rw [ev_res z _ hz h, map_sub, map_zero, H S z h hz, sub_self]
  obtain ⟨n₀, hn₀⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Z hU (x - y) f e
  refine ⟨n₀, fun n hn => ?_⟩
  rw [← sub_eq_zero, ← mul_sub, ← Nat.sub_add_cancel hn, pow_add, mul_assoc, hn₀, mul_zero]

theorem Coc.exists_emb_of_ratio (C : Coc Z) [Finite C.A] (r : ∀ d : C.A, C.A → Γ(Z, C.B d))
    (hb : ∀ d g, Z.basicOpen (r d g) = C.B d ⊓ C.B g) (hs : ∀ d, r d d = 1)
    (hm : ∀ (d e g : C.A) (S : Type) [CommRing S] (z : Sp S ⟶ Z) (hd : ⊤ ≤ z ⁻¹ᵁ C.B d) (he : ⊤ ≤ z ⁻¹ᵁ C.B e),
      ev z _ hd (r d e) * ev z _ he (r e g) = ev z _ hd (r d g)) : ∃ N, Nonempty (C.Emb N) := by
  classical
  have := Fintype.ofFinite C.A
  choose m₀ hm₀ using fun p : Σ g : C.A, Σ d : C.A, Fin (C.n g) × Fin (C.n d) =>
    exists_ev_eq_pow_mul (C.aff p.2.1) (r p.2.1 p.1) ((hb _ _).trans (inf_comm _ _)) (C.T p.1 p.2.1 p.2.2.1 p.2.2.2)
  obtain ⟨m, hmm⟩ : ∃ m, ∀ p, m₀ p ≤ m := ⟨Finset.univ.sup m₀, fun p => Finset.le_sup (Finset.mem_univ p)⟩
  choose Y₀ hY₀ using fun p => hm₀ p m (hmm p)
  obtain ⟨Y, hY⟩ : ∃ Y : ∀ g d : C.A, Matrix (Fin (C.n g)) (Fin (C.n d)) Γ(Z, C.B d),
      ∀ g d (S : Type) [CommRing S] (z : Sp S ⟶ Z) (hg : ⊤ ≤ z ⁻¹ᵁ C.B g) (hd : ⊤ ≤ z ⁻¹ᵁ C.B d),
        (Y g d).map (ev z _ hd) = ev z _ hd (r d g) ^ m • C.tr g d z hg hd :=
    ⟨fun g d => Matrix.of fun i j => Y₀ ⟨g, d, i, j⟩, fun g d S _ z hg hd => Matrix.ext fun i j =>
      hY₀ ⟨g, d, i, j⟩ S z hd (le_preimage_inf hg hd)⟩
  have hY1 : ∀ g, Y g g = 1 := fun g => Matrix.ext fun i j => ext_ev fun S _ z hz => by
    have e := hY g g S z hz hz
    rw [hs, map_one, one_pow, one_smul, C.tr_self] at e
    exact (congrFun (congrFun e i) j).trans
      (congrFun (congrFun (Matrix.map_one _ (map_zero (ev z _ hz)) (map_one _)) i) j).symm
  have key : ∀ g d e, ∀ i j, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Z)
      (hd : ⊤ ≤ z ⁻¹ᵁ C.B d) (he : ⊤ ≤ z ⁻¹ᵁ C.B e),
      ev z _ hd (r d g) ^ n * ((Y g d).map (ev z _ hd) * C.tr d e z hd he) i j =
        ev z _ hd (r d g) ^ n * (ev z _ hd (r d e) ^ m * ev z _ he (Y g e i j)) := by
    intro g d e i j
    have ha : IsAffineOpen (C.B d ⊓ C.B e) := hb d e ▸ (C.aff d).basicOpen (r d e)
    have e₁ : ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Z) (hd : ⊤ ≤ z ⁻¹ᵁ C.B d) (he : ⊤ ≤ z ⁻¹ᵁ C.B e),
        ev z _ (le_preimage_inf hd he) (((Y g d).map (resG Z (inf_le_left : C.B d ⊓ C.B e ≤ C.B d)) * C.T d e) i j) =
          ((Y g d).map (ev z _ hd) * C.tr d e z hd he) i j := fun S _ z hd he => by
      rw [Matrix.mul_apply, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, Matrix.map_apply, ev_res z _ _ hd]
      rfl
    have e₂ : ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Z) (hd : ⊤ ≤ z ⁻¹ᵁ C.B d) (he : ⊤ ≤ z ⁻¹ᵁ C.B e),
        ev z _ (le_preimage_inf hd he) (resG Z inf_le_left (r d e) ^ m * resG Z inf_le_right (Y g e i j)) =
          ev z _ hd (r d e) ^ m * ev z _ he (Y g e i j) := fun S _ z hd he => by
      rw [map_mul, map_pow, ev_res z _ _ hd, ev_res z _ _ he]
    obtain ⟨n₀, hn₀⟩ := exists_pow_mul_eq_of_ev ha (resG Z inf_le_left (r d g))
      (((Y g d).map (resG Z (inf_le_left : C.B d ⊓ C.B e ≤ C.B d)) * C.T d e) i j)
      (resG Z inf_le_left (r d e) ^ m * resG Z inf_le_right (Y g e i j)) fun S _ z h h' => by
        have hd := le_preimage_mono inf_le_left h
        have he := le_preimage_mono inf_le_right h
        have hle : Z.basicOpen (resG Z (inf_le_left : C.B d ⊓ C.B e ≤ C.B d) (r d g)) ≤ C.B g :=
          (Z.basicOpen_res (r d g) (homOfLE inf_le_left).op).le.trans
            (inf_le_right.trans ((hb d g).le.trans inf_le_right))
        have hg := le_preimage_mono hle h'
        refine (e₁ S z hd he).trans (Eq.trans ?_ (e₂ S z hd he).symm)
        have e₃ : ev z _ he (Y g e i j) = ev z _ he (r e g) ^ m * C.tr g e z hg he i j :=
          congrFun (congrFun (hY g e S z hg he) i) j
        rw [hY g d S z hg hd, Matrix.smul_mul, C.tr_mul, e₃, ← mul_assoc, ← mul_pow, hm]
        rfl
    refine ⟨n₀, fun n hn S _ z hd he => ?_⟩
    have e₄ := congrArg (ev z _ (le_preimage_inf hd he)) (hn₀ n hn)
    rwa [map_mul, e₁ S z hd he, map_mul, e₂ S z hd he, map_pow, ev_res z _ _ hd] at e₄
  choose n₀ hn₀ using fun p : Σ g : C.A, Σ _ : C.A, Σ e : C.A, Fin (C.n g) × Fin (C.n e) =>
    key p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  obtain ⟨n, hn⟩ : ∃ n, ∀ p, n₀ p ≤ n := ⟨Finset.univ.sup n₀, fun p => Finset.le_sup (Finset.mem_univ p)⟩
  let q : Option (Σ g : C.A, Fin (C.n g)) ≃ Fin (Fintype.card (Σ g : C.A, Fin (C.n g)) + 1) :=
    Fintype.equivFinOfCardEq Fintype.card_option
  let A : ∀ d, Option (Σ g : C.A, Fin (C.n g)) → Fin (C.n d) → Γ(Z, C.B d) := fun d o j =>
    o.elim 0 fun p => r d p.1 ^ n * Y p.1 d p.2 j
  refine ⟨_, ⟨⟨fun d => Matrix.of fun k j => A d (q.symm k) j,
    fun d => ⟨Matrix.of fun i k => if k = q (some ⟨d, i⟩) then 1 else 0, Matrix.ext fun i j => ?_⟩,
    fun d e S _ z hd he => ?_⟩⟩⟩
  · simp [Matrix.mul_apply, A, hs, hY1]
  · have hu : IsUnit (ev z _ hd (r d e)) := IsUnit.of_mul_eq_one _ ((hm d e d S z hd he).trans (by rw [hs, map_one]))
    refine ⟨hu.unit ^ (m + n), Matrix.ext fun k j => ?_⟩
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, Units.val_pow_eq_pow_val,
      IsUnit.unit_spec, smul_eq_mul]
    rcases q.symm k with _ | ⟨g, i⟩
    · simp [A]
    · have e₅ := hn₀ ⟨g, d, e, i, j⟩ n (hn _) S z hd he
      simp only [Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum, ← mul_assoc] at e₅
      simp only [A, Option.elim_some, map_mul, map_pow]
      rw [e₅, ← hm d e g S z hd he]
      ring

theorem Coc.exists_refine_emb : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (Z : Scheme.{0}) (s : Z ⟶ Sp O),
    IsProjOver s → ∀ C : Coc Z, ∃ (Γ : Type) (a : Γ → C.A) (D : Γ → Z.Opens) (aff : ∀ g, IsAffineOpen (D g))
      (cover : ∀ x : Z, ∃ g, x ∈ D g) (le : ∀ g, D g ≤ C.B (a g)) (N : ℕ),
      Nonempty ((C.refine a D aff cover le).Emb N) := by
  intro O _ _ Z s hZ C
  classical
  obtain ⟨L, hL⟩ := exists_isAmpleLB_of_isProjOver hZ
  have := hL.compactSpace
  choose a ha using C.cover
  choose n hn t hx hle haff using fun x => hL.exists_affine_le (ha x)
  obtain ⟨F, hF⟩ := (isCompact_univ (X := Z)).elim_finite_subcover
    (fun x => (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (t x) : Set Z)) (fun x => (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (t x)).isOpen)
    fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩
  have hd : ∀ g : F, ∃ u : (lbPow L (∏ x ∈ F, n x)).Sec,
      ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (t g.1) := fun g => by
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n g.2
    have hk0 : 1 ≤ k := Nat.pos_of_ne_zero fun h => (Finset.prod_pos fun x _ => hn x).ne' (by rw [hk, h, mul_zero])
    exact ⟨secCast hk.symm (secPow (t g.1) k), (nonzeroLocus_secCast _ _).trans (nonzeroLocus_secPow _ hk0)⟩
  choose u hu using hd
  have cover : ∀ x : Z, ∃ g, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (u g) := fun x => by
    obtain ⟨y, hy, h⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
    exact ⟨⟨y, hy⟩, (hu ⟨y, hy⟩).ge h⟩
  refine ⟨F, fun g => a g.1, fun g => ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (u g), fun g => (congrArg IsAffineOpen (hu g)).mpr (haff g.1), cover,
    fun g => (hu g).le.trans (hle g.1), ?_⟩
  refine @Coc.exists_emb_of_ratio Z _ (inferInstanceAs (Finite F)) (fun d g => ProjSpace.secRatio (u d) (u g))
    (fun d g => ProjSpace.basicOpen_secRatio _ _) (fun d => ProjSpace.secRatio_self _) fun d e g S _ z hd he => ?_
  have h := congrArg (ev z _ (le_preimage_inf hd he))
    (ProjSpace.secRatio_mul_secRatio (u d) (u e) (u g) inf_le_left inf_le_right)
  exact ((congrArg₂ (· * ·) (ev_res z _ _ hd _) (ev_res z _ _ he _)).symm.trans
    ((map_mul _ _ _).symm.trans h)).trans (ev_res z _ _ hd _)

end GlobalTheory.DRFlag
