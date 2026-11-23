import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches
import Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsAlg
import Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsSch
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar CovSch CovAlg

namespace Cov

variable {X Y : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Sp Ω ⟶ X} {ξ₀ : Sp Ω₀ ⟶ Y} {f : X ⟶ Y}
  {fn : Ω₀ →+* Ω}

theorem centre_eq (hdom : ξ ≫ f = spMap fn ≫ ξ₀) : centre (ξ ≫ f) = centre ξ₀ := by
  rw [hdom, centre_spMap]

theorem val_pull (hdom : ξ ≫ f = spMap fn ≫ ξ₀) (U : Y.Opens) (h₀ : centre ξ₀ ∈ U) (W : X.Opens)
    (hW : W ≤ f ⁻¹ᵁ U) (h : centre ξ ∈ W) (r : Γ(Y, U)) :
    val ξ W h ((f.appLE U W hW).hom r) = fn (val ξ₀ U h₀ r) := by
  rw [val_comp ξ f U W hW h (by rw [centre_eq hdom]; exact h₀),
    val_congr hdom U _ (by rw [centre_spMap]; exact h₀), val_spMap fn ξ₀ U h₀]

theorem val_of_point (hξ : IsCptGen ξ) (hall : ∀ q : X, genPt ξ ⤳ q) (hn : IsNormalScheme X)
    (hdom : ξ ≫ f = spMap fn ≫ ξ₀) (U : Y.Opens) (h₀ : centre ξ₀ ∈ U) (θ : Ω) (P : Γ(Y, U)[X]) (hP : P.Monic)
    (hθ : eval₂ (fn.comp (val ξ₀ U h₀)) θ P = 0) (z : Sp ℂ ⟶ X) (hz : centre (z ≫ f) ∈ U) :
    ∃ θ₀ : ℂ, ∀ G : Γ(Y, U)[X], ValAt ξ z (eval₂ (fn.comp (val ξ₀ U h₀)) θ G) (eval₂ (val (z ≫ f) U hz) θ₀ G) := by
  let q : Cpt ξ := ⟨centre z, hall _⟩
  have hq : centre z ∈ f ⁻¹ᵁ U := hz
  have hg : centre ξ ∈ f ⁻¹ᵁ U := by
    have : centre (ξ ≫ f) ∈ U := by rw [centre_eq hdom]; exact h₀
    exact this
  let ρ : Γ(Y, U) →+* X.presheaf.stalk (centre z) :=
    (X.presheaf.germ (f ⁻¹ᵁ U) (centre z) hq).hom.comp (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom
  let j : X.presheaf.stalk (centre z) →+* Ω := genMap ξ q
  let e : X.presheaf.stalk (centre z) →+* ℂ := (Scheme.stalkClosedPointTo z).hom
  have h1 : j.comp ρ = fn.comp (val ξ₀ U h₀) := RingHom.ext fun r =>
    (genMap_germ' q _ hq hg _).trans (val_pull hdom U h₀ _ le_rfl hg r)
  have h2 : e.comp ρ = val (z ≫ f) U hz := RingHom.ext fun r => val_comp z f U _ le_rfl hq hz r
  obtain ⟨τ, hτ⟩ : ∃ τ, j τ = θ := by
    have := (hn (centre z)).1
    have := (hn (centre z)).2
    let _ : Algebra (X.presheaf.stalk (centre z)) Ω := j.toAlgebra
    have : FaithfulSMul (X.presheaf.stalk (centre z)) Ω :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (hξ.inj q)
    have : IsFractionRing (X.presheaf.stalk (centre z)) Ω := IsFractionRing.of_field _ _ fun x => by
      obtain ⟨⟨_, a, rfl⟩, ⟨_, b, rfl⟩, h⟩ := RegAtRing.exists_div hξ q x
      exact ⟨a, b, h⟩
    refine IsIntegrallyClosed.isIntegral_iff.1 ⟨P.map ρ, hP.map ρ, ?_⟩
    rw [eval₂_map]
    exact (congrArg (fun φ => eval₂ φ θ P) h1).trans hθ
  refine ⟨e τ, fun G => ⟨hall _, eval₂ ρ τ G, ?_, ?_⟩⟩
  · show j _ = _
    rw [hom_eval₂, h1, hτ]
  · show e _ = _
    rw [hom_eval₂, h2]

theorem point_of_root (hξ : IsCptGen ξ) (hall : ∀ q : X, genPt ξ ⤳ q) (hdom : ξ ≫ f = spMap fn ≫ ξ₀)
    {U U₀ : Y.Opens} (hU₀ : IsAffineOpen U₀) (hU : U ≤ U₀) (h₀ : centre ξ₀ ∈ U) {W : X.Opens} (hW : IsAffineOpen W)
    (hWU : W ≤ f ⁻¹ᵁ U₀) (h : centre ξ ∈ W) (θ : Ω)
    (hr : ∀ a, ∃ G : Γ(Y, U)[X], eval₂ (fn.comp (val ξ₀ U h₀)) θ G = val ξ W h a) (p : Sp ℂ ⟶ Y)
    (hp : centre p ∈ U) (θ₀ : ℂ)
    (key : ∀ G : Γ(Y, U)[X], eval₂ (fn.comp (val ξ₀ U h₀)) θ G = 0 → eval₂ (val p U hp) θ₀ G = 0) :
    ∃ z : Sp ℂ ⟶ X, centre z ∈ W ∧ z ≫ f = p ∧ ∀ G : Γ(Y, U)[X],
      eval₂ (fn.comp (val ξ₀ U h₀)) θ G ∈ regAt ξ ⟨centre z, hall _⟩ →
        ValAt ξ z (eval₂ (fn.comp (val ξ₀ U h₀)) θ G) (eval₂ (val p U hp) θ₀ G) := by
  let ev : Γ(Y, U)[X] →+* Ω := eval₂RingHom (fn.comp (val ξ₀ U h₀)) θ
  let ev₀ : Γ(Y, U)[X] →+* ℂ := eval₂RingHom (val p U hp) θ₀
  let φ : ev.range →+* ℂ := RingHom.liftOfSurjective ev.rangeRestrict ev.rangeRestrict_surjective
    ⟨ev₀, fun G hG => key G (congrArg Subtype.val (RingHom.mem_ker.1 hG))⟩
  have hφ : ∀ G, φ (ev.rangeRestrict G) = ev₀ G := fun G => RingHom.liftOfRightInverse_comp_apply _ _ _ _ G
  let χ : Γ(X, W) →+* ℂ := φ.comp ((val ξ W h).codRestrict ev.range hr)
  have hχ : ∀ a G, ev G = val ξ W h a → χ a = ev₀ G := fun a G e => by
    rw [← hφ]
    exact congrArg φ (Subtype.ext e.symm)
  obtain ⟨z, hz, hv⟩ := exists_of_hom hW χ
  refine ⟨z, hz, eq_of_val hU₀ (hWU hz) (hU hp) fun r => ?_, fun G hG => ?_⟩
  · refine (val_comp z f U₀ W hWU hz _ r).symm.trans ?_
    rw [hv, hχ _ (C ((Y.presheaf.map (homOfLE hU).op).hom r))]
    · simp only [ev₀, coe_eval₂RingHom, eval₂_C]
      exact val_res p hU hp r
    · rw [val_pull hdom U₀ (hU h₀) W hWU h]
      simp only [ev, coe_eval₂RingHom, eval₂_C, RingHom.comp_apply]
      exact congrArg fn (val_res ξ₀ hU h₀ r)
  · obtain ⟨g, hg⟩ := hG
    obtain ⟨a, b, hb, hab⟩ := exists_frac hW z hz g
    refine ⟨hall _, g, hg, ?_⟩
    have e1 : (Scheme.stalkClosedPointTo z).hom g * val z W hz b = val z W hz a :=
      (map_mul _ _ _).symm.trans (congrArg (Scheme.stalkClosedPointTo z).hom hab)
    have e2 : ev G * val ξ W h b = val ξ W h a := by
      have := congrArg (genMap ξ ⟨centre z, hall _⟩) hab
      rw [map_mul, genMap_germ' ⟨centre z, hall _⟩ W hz h, genMap_germ' ⟨centre z, hall _⟩ W hz h, hg] at this
      exact this
    obtain ⟨Gb, hGb⟩ := hr b
    have e3 : χ a = ev₀ G * χ b := by
      rw [hχ b Gb hGb, ← map_mul]
      exact hχ a _ (by rw [map_mul, ← e2]; exact congrArg _ hGb)
    rw [hv] at hb
    rw [hv, hv, e3] at e1
    exact mul_right_cancel₀ hb e1

theorem root_iff {R : Type} [CommRing R] {d : ℕ} (a : Fin d → R) (ψ : R →+* ℂ) (x : ℂ) :
    (monicOf fun i => ψ (a i)).IsRoot x ↔ eval₂ ψ x (mon a) = 0 := by
  rw [eval₂_eq_eval_map, mon_map]
  rfl

theorem cover {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} [CharZero Ω]
    [IsLocallyNoetherian Y] (T : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)
    (hall : ∀ q : X, genPt ξ ⤳ q) (hn : IsNormalScheme X) (hξ₀ : IsCptGen ξ₀) (hdom : ξ ≫ f = spMap fn ≫ ξ₀)
    (d : ℕ) (hd : 0 < d) (hfin : letI := fn.toAlgebra; Module.finrank Ω₀ Ω = d) :
    ∃ (U : Y.Opens) (a : Fin d → Γ(Y, U)) (cf : (Σ k, J k) → Fin d → Γ(Y, U)), centre ξ₀ ∈ U ∧
      ∀ (p : Sp ℂ ⟶ Y) (hp : centre p ∈ U), (monicOf fun i => val p U hp (a i)).Separable ∧
        (∀ θ, (monicOf fun i => val p U hp (a i)).IsRoot θ → ∃ z : Sp ℂ ⟶ X, z ≫ f = p ∧
          CoordsAt ξ y z fun s => ∑ i, val p U hp (cf s i) * θ ^ (i : ℕ)) ∧
        (∀ z : Sp ℂ ⟶ X, z ≫ f = p → ∃ θ, (monicOf fun i => val p U hp (a i)).IsRoot θ ∧
          CoordsAt ξ y z fun s => ∑ i, val p U hp (cf s i) * θ ^ (i : ℕ)) ∧
        ∀ θ θ' (z : Sp ℂ ⟶ X), (monicOf fun i => val p U hp (a i)).IsRoot θ →
          (monicOf fun i => val p U hp (a i)).IsRoot θ' →
          (CoordsAt ξ y z fun s => ∑ i, val p U hp (cf s i) * θ ^ (i : ℕ)) →
          (CoordsAt ξ y z fun s => ∑ i, val p U hp (cf s i) * θ' ^ (i : ℕ)) → θ = θ' := by
  classical
  have hξ := T.gen
  let _ := fn.toAlgebra
  obtain ⟨c, hc⟩ := T.cover ⟨genPt ξ, specializes_rfl⟩
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  obtain ⟨W, hW, hWm⟩ := T.affine c hc.1
  have hηW : centre ξ ∈ W := (hWm _).2 ⟨specializes_rfl, hc⟩
  let t : (Σ k, J k) → Ω := fun s => y s / y ⟨s.1, c s.1⟩
  have hreg : ∀ q : X, q ∈ W → ∀ s, t s ∈ regAt ξ ⟨q, hall q⟩ := by
    rintro q hq ⟨k, i⟩
    obtain ⟨_, -, h2⟩ := (hWm q).1 hq
    have h3 := h2 (Function.update c k i)
    have e : (∏ l, y ⟨l, Function.update c k i l⟩) / (∏ l, y ⟨l, c l⟩) = t ⟨k, i⟩ := by
      rw [← Finset.prod_div_distrib, Finset.prod_eq_single k (fun l _ hl => by
        rw [Function.update_of_ne hl, div_self (hy l)]) (by simp), Function.update_self]
    exact e ▸ h3
  have hA : ∀ B : Subring Ω, (∀ s, t s ∈ B) → ∀ a, val ξ W hηW a ∈ B := by
    intro B hB a
    have h1 := (T.ring c hc.1 (val ξ W hηW a)).2 fun q hq =>
      ⟨_, genMap_germ' q W ((hWm q.1).2 ⟨q.2, hq⟩) hηW a⟩
    have h2 : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤
        subalgebraOfSubring B := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨j, rfl⟩
      show (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩ ∈ B
      rw [← Finset.prod_div_distrib]
      exact prod_mem fun k _ => hB ⟨k, j k⟩
    exact h2 h1
  have ht : Algebra.adjoin Ω₀ (Set.range t) = ⊤ := by
    have : FiniteDimensional Ω₀ Ω := Module.finite_of_finrank_pos (hfin ▸ hd)
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨g, rfl⟩ := hξ.bij.2 x
    obtain ⟨a, b, hb, hab⟩ := exists_frac hW ξ hηW g
    have e1 : (Scheme.stalkClosedPointTo ξ).hom g * val ξ W hηW b = val ξ W hηW a :=
      (map_mul _ _ _).symm.trans (congrArg (Scheme.stalkClosedPointTo ξ).hom hab)
    have hm := hA (Algebra.adjoin Ω₀ (Set.range t)).toSubring fun s => Algebra.subset_adjoin ⟨s, rfl⟩
    rw [(eq_mul_inv_iff_mul_eq₀ hb).2 e1]
    exact mul_mem (hm a) (Subalgebra.inv_mem_of_algebraic _ (x := ⟨_, hm b⟩) (Algebra.IsAlgebraic.isAlgebraic _))
  obtain ⟨U₀, hU₀, hη₀, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := centre ξ₀) (U := ⊤) trivial
  have hηf : centre ξ ∈ f ⁻¹ᵁ U₀ := by
    have : centre (ξ ≫ f) ∈ U₀ := by rw [centre_eq hdom]; exact hη₀
    exact this
  obtain ⟨g, hgU, hηg⟩ := hW.exists_basicOpen_le (V := f ⁻¹ᵁ U₀) ⟨centre ξ, hηf⟩ hηW
  obtain ⟨θ, S, hS, hmain⟩ := exists_prim Ω₀ Ω d hd hfin t ht (val ξ W hηW g)⁻¹
  obtain ⟨Uc, hUc, -⟩ := Flat.cpt_open_integral Y Ω₀ ξ₀ hξ₀
  obtain ⟨U, h₀, hUle, hSU⟩ := exists_open hξ₀ S hS (U₀ ⊓ Uc) ⟨hη₀, (hUc _).2 specializes_rfl⟩
  obtain ⟨a, cf, G, Q, hsep, hker, hcf, hG, hQ⟩ := hmain Γ(Y, U) (val ξ₀ U h₀)
    (val_injective hξ₀ U h₀ fun q hq => (hUc q).1 (hUle hq).2) hSU
  have hfn : algebraMap Ω₀ Ω = fn := rfl
  rw [hfn] at hker hcf hG hQ
  let ev : Γ(Y, U)[X] →+* Ω := eval₂RingHom (fn.comp (val ξ₀ U h₀)) θ
  have hr : ∀ s, ∃ G : Γ(Y, U)[X], eval₂ (fn.comp (val ξ₀ U h₀)) θ G = val ξ (X.basicOpen g) hηg s := by
    intro s
    have := hW.isLocalization_basicOpen g
    obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj g s
    have e1 := congrArg (val ξ (X.basicOpen g) hηg) hb
    rw [map_mul, map_pow] at e1
    have e2 : ∀ b, val ξ (X.basicOpen g) hηg (algebraMap Γ(X, W) Γ(X, X.basicOpen g) b) = val ξ W hηW b :=
      fun b => val_res ξ (X.basicOpen_le g) hηg b
    have hg0 : val ξ W hηW g ≠ 0 := by
      rw [← e2]
      exact ((IsLocalization.Away.algebraMap_isUnit g).map _).ne_zero
    rw [e2, e2] at e1
    have hm := hA ev.range fun s => ⟨_, hcf s⟩
    have : val ξ (X.basicOpen g) hηg s ∈ ev.range := by
      rw [(eq_mul_inv_iff_mul_eq₀ (pow_ne_zero n hg0)).2 e1, ← inv_pow]
      exact mul_mem (hm b) (pow_mem (show _ ∈ ev.range from ⟨G, hG⟩) n)
    exact this
  refine ⟨U, a, cf, h₀, fun p hp => ?_⟩
  have key : ∀ x, eval₂ (val p U hp) x (mon a) = 0 → ∀ G : Γ(Y, U)[X],
      eval₂ (fn.comp (val ξ₀ U h₀)) θ G = 0 → eval₂ (val p U hp) x G = 0 := by
    intro x hx G hG
    obtain ⟨H, rfl⟩ := (hker G).1 hG
    rw [eval₂_mul, hx, zero_mul]
  have key' : ∀ x, eval₂ (val p U hp) x (mon a) = 0 → ∀ G G' : Γ(Y, U)[X],
      eval₂ (fn.comp (val ξ₀ U h₀)) θ G = eval₂ (fn.comp (val ξ₀ U h₀)) θ G' →
        eval₂ (val p U hp) x G = eval₂ (val p U hp) x G' := by
    intro x hx G G' e
    rw [← sub_eq_zero, ← eval₂_sub]
    exact key x hx _ (by rw [eval₂_sub, e, sub_self])
  have hone : ∀ x, eval₂ (val p U hp) x (mon a) = 0 → ∀ k,
      ∑ i, val p U hp (cf ⟨k, c k⟩ i) * x ^ (i : ℕ) = 1 := by
    intro x hx k
    rw [← eval₂_low, key' x hx _ 1 (by rw [hcf, eval₂_one]; exact div_self (hy k)), eval₂_one]
  simp only [root_iff]
  refine ⟨?_, fun x hx => ?_, fun z hz => ?_, fun x x' z hx hx' hc1 hc2 => ?_⟩
  · have := hsep.map (f := val p U hp)
    rw [mon_map] at this
    exact this
  · obtain ⟨z, hz, hzp, hv⟩ := point_of_root hξ hall hdom hU₀ (hUle.trans inf_le_left) h₀ (hW.basicOpen g) hgU hηg θ
      hr p hp x (key x hx)
    refine ⟨z, hzp, coordsAt_of_val c hy (fun s => ?_) (hone x hx)⟩
    have := hv (low (cf s)) (by rw [hcf]; exact hreg _ (X.basicOpen_le g hz) s)
    rwa [hcf, eval₂_low] at this
  · subst hz
    obtain ⟨x, hv⟩ := val_of_point hξ hall hn hdom U h₀ θ (mon a) (mon_monic a) ((hker _).2 dvd_rfl) z hp
    have hx : eval₂ (val (z ≫ f) U hp) x (mon a) = 0 := by
      have h1 := hv (mon a)
      have h2 := hv 0
      rw [(hker _).2 dvd_rfl] at h1
      rw [eval₂_zero, eval₂_zero] at h2
      exact v_unique hξ h1 h2
    refine ⟨x, hx, coordsAt_of_val c hy (fun s => ?_) (hone x hx)⟩
    have := hv (low (cf s))
    rwa [hcf, eval₂_low] at this
  · have hw : ∀ s, eval₂ (val p U hp) x (low (cf s)) = eval₂ (val p U hp) x' (low (cf s)) := fun s => by
      rw [eval₂_low, eval₂_low]
      exact v_unique hξ (val_of_coordsAt c hc1 (hone x hx) s) (val_of_coordsAt c hc2 (hone x' hx') s)
    have hev : ∀ {S : Type} [CommRing S] (φ : Γ(Y, U) →+* S) (u : S),
        eval₂ φ u (MvPolynomial.eval₂ C (fun s => low (cf s)) Q) =
          MvPolynomial.eval₂ φ (fun s => eval₂ φ u (low (cf s))) Q := by
      intro S _ φ u
      have := MvPolynomial.eval₂_comp_left (eval₂RingHom φ u) C (fun s => low (cf s)) Q
      rw [show (eval₂RingHom φ u).comp C = φ from RingHom.ext fun r => eval₂_C _ _] at this
      exact this
    have hX : ∀ u, eval₂ (val p U hp) u (mon a) = 0 →
        u = MvPolynomial.eval₂ (val p U hp) (fun s => eval₂ (val p U hp) u (low (cf s))) Q := by
      intro u hu
      rw [← hev, key' u hu _ Polynomial.X (by rw [hev, eval₂_X, funext hcf, hQ]), eval₂_X]
    rw [hX x hx, funext hw, ← hX x' hx']

end Cov

theorem coverRoots : CoverRoots := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 d hd
  have := c.fin
  have : NumberField c.F := {}
  have : IsLocallyNoetherian Y.X := by
    obtain ⟨N, i, hi, e⟩ := Y.proj
    have := isProper_str (𝓞 c.F) N
    have : LocallyOfFiniteType Y.s := e ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian Y.s
  obtain ⟨U, a, cf, h₀, h⟩ := Cov.cover 𝔐.tie 𝔐.all 𝔐.normal 𝔐.gen₀ 𝔐.fn_over d hd.1 hd.2
  refine ⟨U, a, cf, h₀, fun p hp => ?_⟩
  have hp' := (top_le_iff p U).1 hp
  simp only [valAt'_eq p U hp']
  exact h p hp'

end SheetDecomposition
