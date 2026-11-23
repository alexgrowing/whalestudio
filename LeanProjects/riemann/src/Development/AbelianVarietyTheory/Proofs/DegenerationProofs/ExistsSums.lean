import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSeriesRingHomExtendingFiniteFreeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRingHomPowerSeriesRootStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxEvEqMapArcRootStatement

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ArcSeries

section Comp
variable {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O''] {f : O →+* O'} {g : O' →+* O''}
  {N : NumD O} {N' : NumD O'} {N'' : NumD O''}

def homComp (I : NumD.Hom f N N') (I' : NumD.Hom g N' N'') (k : O →+* O'') (hk : ∀ x, k x = g (f x)) :
    NumD.Hom k N N'' :=
  have e : ∀ x : Oˣ, Units.map k.toMonoidHom x = Units.map g.toMonoidHom (Units.map f.toMonoidHom x) :=
    fun x => Units.ext (hk x)
  { φ := I'.φ.comp I.φ
    h x := I'.h (I.φ x) * Units.map g.toMonoidHom (I.h x)
    h_one := by rw [map_one, I'.h_one, I.h_one, map_one, mul_one]
    θ_eq x y u := by
      have a := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (I.θ_eq x y u)
      have b := congrArg Additive.ofMul (I'.θ_eq (I.φ x) (I.φ y) (I.φ u))
      apply Additive.ofMul.injective
      simp only [e, map_mul, ofMul_mul, MonoidHom.comp_apply] at a b ⊢
      linear_combination (norm := abel) a + b
    σ_eq x := by
      have a := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (I.σ_eq x)
      have b := congrArg Additive.ofMul (I'.σ_eq (I.φ x))
      apply Additive.ofMul.injective
      simp only [e, map_mul, map_inv, ofMul_mul, MonoidHom.comp_apply] at a b ⊢
      linear_combination (norm := abel) a + b
    lam := I'.lam * Units.map g.toMonoidHom I.lam
    th_eq x := by
      rw [MonoidHom.comp_apply, I'.th_eq, I.th_eq, hk]
      simp only [Units.val_mul, map_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      ring
    e := I.e.trans I'.e
    c_eq χ := by rw [AddEquiv.trans_apply, I'.c_eq, I.c_eq]; rfl
    ψ_eq χ := by
      have a := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (I.ψ_eq χ)
      have b := congrArg Additive.ofMul (I'.ψ_eq (I.e χ))
      apply Additive.ofMul.injective
      simp only [e, map_mul, ofMul_mul, AddEquiv.trans_apply, I.c_eq] at a b ⊢
      linear_combination (norm := abel) a + b }

theorem homComp_rel (I : NumD.Hom f N N') (I' : NumD.Hom g N' N'') (k : O →+* O'') (hk : ∀ x, k x = g (f x))
    {a : N.Gt} {b : N'.Gt} {c : N''.Gt} (h : I.Rel a b) (h' : I'.Rel b c) : (homComp I I' k hk).Rel a c := by
  refine ⟨h'.1.trans (congrArg I'.φ h.1), fun χ => ?_⟩
  have e : ∀ x : Oˣ, Units.map k.toMonoidHom x = Units.map g.toMonoidHom (Units.map f.toMonoidHom x) :=
    fun x => Units.ext (hk x)
  have p := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (h.2 χ)
  have q := congrArg Additive.ofMul (h'.2 (I.e χ))
  apply Additive.ofMul.injective
  simp only [homComp, e, map_mul, ofMul_mul, AddEquiv.trans_apply, I.c_eq, h.1] at p q ⊢
  linear_combination (norm := abel) p + q
end Comp

theorem exists_ball (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 :=
  ⟨(NormedField.valuation (K := C)).valuationSubring, fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]; exact Iff.rfl⟩

theorem mem_of_isIntegral {R K : Type} [CommRing R] [Field K] [Algebra R K] (S : ValuationSubring K)
    (h : ∀ r, algebraMap R K r ∈ S) {x : K} (hx : IsIntegral R x) : x ∈ S := by
  have : IsIntegral S x := hx.map_of_comp_eq ((algebraMap R K).codRestrict S h) (RingHom.id K) rfl
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
  exact y.2

theorem exists_map {O O₁ K : Type} [CommRing O] [CommRing O₁] [Field K] [Algebra O O₁] [Module.Free O O₁]
    [Module.Finite O O₁] [Algebra (PowerSeries O) K] (io : O₁ →+* K)
    (hio : ∀ a, io (algebraMap O O₁ a) = algebraMap (PowerSeries O) K (PowerSeries.C a)) {k : ℕ} (hk : 0 < k) {t : K}
    (ht : t ^ k = algebraMap (PowerSeries O) K PowerSeries.X) :
    ∃ (R₁ : Subalgebra (PowerSeries O) K) (Φ : PowerSeries O₁ →+* K), Module.Finite (PowerSeries O) R₁ ∧
      (∀ a, Φ (PowerSeries.C a) = io a) ∧ Φ PowerSeries.X = t ∧ ∀ f, Φ f ∈ R₁ := by
  obtain ⟨Φ₁, h1, h2, h3⟩ := GlobalTheory.T.exists_powerSeries_ringHom_extending_finite_free O O₁ K (algebraMap _ K) io hio
  obtain ⟨Φ, h4, h5, h6⟩ := GlobalTheory.T.exists_ringHom_powerSeries_root' O₁ K Φ₁ k t hk (ht.trans h2.symm)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := O₁)
  refine ⟨Algebra.adjoin _ (io '' s ∪ {t}), Φ, Algebra.finite_adjoin_of_finite_of_isIntegral
    ((s.finite_toSet.image _).union (Set.finite_singleton _)) ?_, fun a => (h4 a).trans (h1 a), h5, fun f => ?_⟩
  · rintro x (⟨a, -, rfl⟩ | rfl)
    · exact (Algebra.IsIntegral.isIntegral (R := O) a).map_of_comp_eq PowerSeries.C io (RingHom.ext fun a => (hio a).symm)
    · exact IsIntegral.of_pow hk (ht ▸ isIntegral_algebraMap)
  · refine (Subring.closure_le (t := (Algebra.adjoin _ (io '' s ∪ {t})).toSubring)).2 ?_ (h6 f)
    rintro x (⟨g, rfl⟩ | rfl)
    · refine (Subring.closure_le (t := (Algebra.adjoin _ (io '' s ∪ {t})).toSubring)).2 ?_ (h3 g)
      rintro x (⟨g, rfl⟩ | ⟨a, rfl⟩)
      · exact Subalgebra.algebraMap_mem _ g
      · have ha : a ∈ Submodule.span O (s : Set O₁) := hs ▸ Submodule.mem_top
        change io a ∈ Algebra.adjoin (PowerSeries O) (io '' s ∪ {t})
        induction ha using Submodule.span_induction with
        | mem x hx => exact Algebra.subset_adjoin (.inl ⟨x, hx, rfl⟩)
        | zero => rw [map_zero]; exact zero_mem _
        | add x y _ _ a b => rw [map_add]; exact add_mem a b
        | smul c x _ a => rw [Algebra.smul_def, map_mul, hio]; exact mul_mem (Subalgebra.algebraMap_mem _ _) a
    · exact Algebra.subset_adjoin (.inr rfl)

def Sums {R K F : Type} [CommRing R] [Field K] [Field F] [Algebra R K] (X : R) (io : F →+* K) (N : NumD F)
    (be : LinearMap.BilinForm ℤ N.X) (m j : ℕ) {La : Type} (q : La → N.QT (m ^ 2)) (qz : N.QT j) (t : Kˣ)
    (v w : La → K) : Prop :=
  ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (gam : K →+* C),
    (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) → ‖gam (algebraMap R K X)‖ < 1 →
    ∀ (N' : NumD C) (I : NumD.Hom (gam.comp io) N N') (k : ℕ) (β : N'.Form k), I.lam = 1 →
    (∀ y z, β.be (I.e y) (I.e z) = be y z) → ∀ u rm rj : Cˣ, (u : C) = gam (algebraMap R K X) →
    (rm : C) = gam (t ^ j : Kˣ) → (rj : C) = gam (t ^ m ^ 2 : Kˣ) →
    ∀ (q' : La → N'.QT (m ^ 2)) (p : La → (N'.twist β u).QT (m ^ 2)),
    (∀ x, (q' x).1.1.toAdd = I.e (q x).1.1.toAdd ∧ I.Rel (q x).1.2 (q' x).1.2) → (∀ x, TwRel β u rm (q' x) (p x)) →
    (∀ x, gam (v x) = (N'.twist β u).tx m (p x)) ∧
    ∀ (qz' : N'.QT j) (pz : (N'.twist β u).QT j), qz'.1.1.toAdd = I.e qz.1.1.toAdd → I.Rel qz.1.2 qz'.1.2 →
      TwRel β u rj qz' pz → ∃ s : Cˣ, ∀ x, gam (w x) = s * (N'.twist β u).ev m (p x) pz.1.2

theorem exists_sums {O O₁ K F : Type} [CommRing O] [CommRing O₁] [Field K] [Field F] [Algebra O O₁] [Module.Free O O₁]
    [Module.Finite O O₁] [Algebra (PowerSeries O) K] (f : O₁ →+* F) (io : F →+* K)
    (hio : ∀ a, io (f (algebraMap O O₁ a)) = algebraMap (PowerSeries O) K (PowerSeries.C a)) {N : NumD F}
    (be : LinearMap.BilinForm ℤ N.X) {m j : ℕ} (hm : Odd m) (hj : 0 < j) {La : Type} (q : La → N.QT (m ^ 2)) (qz : N.QT j)
    (t : Kˣ) (ht : (t : K) ^ (m ^ 2 * j) = algebraMap (PowerSeries O) K PowerSeries.X) {N₀ : NumD O₁}
    (I₀ : NumD.Hom f N₀ N) (hl : I₀.lam = 1)
    (hq : ∀ x, ∃ p₀ : N₀.QT (m ^ 2), (q x).1.1.toAdd = I₀.e p₀.1.1.toAdd ∧ I₀.Rel p₀.1.2 (q x).1.2)
    (hz : ∃ p₀ : N₀.QT j, qz.1.1.toAdd = I₀.e p₀.1.1.toAdd ∧ I₀.Rel p₀.1.2 qz.1.2) :
    ∃ (R₁ : Subalgebra (PowerSeries O) K) (v w : La → K), Module.Finite (PowerSeries O) R₁ ∧ (∀ x, v x ∈ R₁) ∧
      Sums (PowerSeries.X : PowerSeries O) io N be m j q qz t v w := by
  have hk : 0 < m ^ 2 * j := Nat.mul_pos (pow_pos hm.pos 2) hj
  obtain ⟨R₁, Φ, hR, h1, h2, h3⟩ := exists_map (io.comp f) hio hk ht
  choose p₀ hp hp' using hq
  obtain ⟨q₀, hz, hz'⟩ := hz
  let be₀ : LinearMap.BilinForm ℤ N₀.X := be.comp I₀.e.toAddMonoidHom.toIntLinearMap I₀.e.toAddMonoidHom.toIntLinearMap
  let s : ℕ := ((m : ℤ) ^ 2 * (((m ^ 2 * j : ℕ) : ℤ) * be₀ q₀.1.1.toAdd q₀.1.1.toAdd)).toNat
  refine ⟨R₁, fun x => Φ (N₀.arcTx (((m ^ 2 * j : ℕ) : ℤ) • be₀) m (p₀ x)),
    fun x => Φ (N₀.arcEv (((m ^ 2 * j : ℕ) : ℤ) • be₀) m (p₀ x) q₀ s), hR, fun x => h3 _, ?_⟩
  intro C _ _ _ gam g1 g2 N' I k β hI hβ u rm rj hu hrm hrj q' p hq' hp''
  obtain ⟨S, hS⟩ := exists_ball C
  have n1 : ∀ g, ‖(gam.comp Φ) g‖ ≤ 1 := fun g => (hS _).1 (mem_of_isIntegral (S.comap gam)
    (fun r => (hS _).2 (g1 r)) ((Algebra.IsIntegral.isIntegral (⟨_, h3 g⟩ : R₁)).map R₁.val))
  have n2 : ‖(gam.comp Φ) PowerSeries.X‖ < 1 := by
    rw [← ht, map_pow, norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg _) hk.ne'] at g2
    rwa [RingHom.comp_apply, h2]
  let t' : Cˣ := Units.map gam.toMonoidHom t
  let J := homComp I₀ I ((gam.comp Φ).comp PowerSeries.C) fun x => congrArg gam (h1 x)
  have hJ : J.lam = 1 := by
    change I.lam * Units.map _ I₀.lam = 1
    rw [hI, hl, map_one, mul_one]
  have e1 : t' ^ j = rm := Units.ext (by rw [hrm, ← map_pow]; rfl)
  have key := fun x => GlobalTheory.T.twist_tx_ev_eq_map_arc_root_alt O₁ C (gam.comp Φ) n1 n2 t' u rm rj m j hm hj (congrArg gam h2.symm) e1
    (Units.ext (by rw [hrj, ← map_pow]; rfl))
    (Units.ext (by rw [hu, ← e1, ← pow_mul, mul_comm j, ← ht, ← map_pow, map_pow gam]; simp [t']))
    N₀ N' J k be₀ β (fun y z => hβ _ _) (p₀ x) (q' x) (p x) ((hq' x).1.trans (congrArg I.e (hp x)))
    (homComp_rel _ _ _ _ (hp' x) (hq' x).2) (hp'' x)
  refine ⟨fun x => ?_, fun qz' pz a b c => ⟨(J.lam * J.h q₀.1.2.b ^ (m ^ 2))⁻¹ * t' ^ s, fun x => ?_⟩⟩
  · rw [(key x).1, hJ, Units.val_one, one_mul]; rfl
  · have := (key x).2 q₀ qz' pz (a.trans (congrArg I.e hz)) (homComp_rel _ _ _ _ hz' b) c s (Int.self_le_toNat _)
    rw [Units.val_mul, mul_assoc, Units.val_pow_eq_pow_val, this, Units.inv_mul_cancel_left]; rfl

end GlobalTheory.ArcSeries
end
