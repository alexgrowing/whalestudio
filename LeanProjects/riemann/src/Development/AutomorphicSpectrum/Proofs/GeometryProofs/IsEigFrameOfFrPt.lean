import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingPadicComplexInt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.RuleVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

section Values

variable (T : Formalism.L2.Pj.CDVR)

theorem norm_eq_zpow {C : Type} [NormedField C] (j : T.Fr →+* C)
    (h1 : ∀ a : T.V, ‖j (algebraMap T.V T.Fr a)‖ ≤ 1) {π : T.V} (hπ : Irreducible π) {x : T.Fr} (hx : x ≠ 0) :
    ‖j x‖ = ‖j (algebraMap T.V T.Fr π)‖ ^ Formalism.L2.Pj.vV T.V x := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hx
  have hu : ‖j (algebraMap T.V T.Fr u)‖ = 1 := by
    have h : ‖j (algebraMap T.V T.Fr u)‖ * ‖j (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    refine le_antisymm (h1 _) ?_
    calc (1 : ℝ) = _ := h.symm
      _ ≤ ‖j (algebraMap T.V T.Fr u)‖ * 1 := mul_le_mul_of_nonneg_left (h1 _) (norm_nonneg _)
      _ = _ := mul_one _
  have hv : Formalism.L2.Pj.vV T.V (u • algebraMap T.V T.Fr π ^ n) = n := by
    rw [Formalism.L2.Pj.vV, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
      GlobalTheory.PlaceCompletion.valV_algebraMap_of_isUnit u.isUnit,
      GlobalTheory.PlaceCompletion.valV_algebraMap_of_irreducible hπ, _root_.one_mul, ← WithZero.exp_zsmul,
      WithZero.log_exp]
    simp
  rw [hv, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, norm_mul, norm_zpow, hu, _root_.one_mul]

theorem norm_le_one_of_mem {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) (h : x ∈ 𝓞_ℂ_[p]) : ‖x‖ ≤ 1 := by
  suffices hs : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 from hs.1 h
  rw [PadicComplex.norm_eq_norm, Valuation.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe,
    ← map_one (Valuation.RankOne.hom (PadicComplex.valued p).v),
    (Valuation.RankOne.strictMono _).le_iff_le, Valuation.restrict_le_one_iff]
  rfl

theorem exists_embed (hT : T.FinRes) :
    ∃ (p : Nat.Primes) (j : T.Fr →+* ℂ_[p]), ∀ a : T.Fr, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap T.V T.Fr).range := by
  obtain ⟨p, hp, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hT
  have h1 : ∀ a : T.V, ‖k (algebraMap T.V T.Fr a)‖ ≤ 1 := fun a => by
    rw [← hk]
    exact (norm_le_one_of_mem _ (kO a).2)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hc0 : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
  have hlt : ‖k (algebraMap T.V T.Fr π)‖ < 1 := by
    by_contra hc
    have he : ‖k (algebraMap T.V T.Fr π)‖ = 1 := le_antisymm (h1 π) (not_lt.mp hc)
    have := norm_eq_zpow T k h1 hπ (x := (p : T.Fr)) (Nat.cast_ne_zero.2 hp.out.ne_zero)
    rw [he, one_zpow, map_natCast] at this
    have h3 : ‖(p : ℂ_[p])‖ < 1 := by
      have e : ((p : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
      rw [e, norm_algebraMap']
      exact Padic.norm_p_lt_one
    exact h3.ne this
  have hpos : 0 < ‖k (algebraMap T.V T.Fr π)‖ := norm_pos_iff.2 ((map_ne_zero k).2
    ((map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hπ.ne_zero))
  refine ⟨⟨p, hp.out⟩, k, fun x => ⟨fun hx => ?_, by rintro ⟨a, rfl⟩; exact h1 a⟩⟩
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  rcases ValuationRing.isInteger_or_isInteger T.V x with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ⟨a, ha⟩
  · by_cases hu : IsUnit a
    · obtain ⟨u, rfl⟩ := hu
      refine ⟨(u⁻¹ : T.Vˣ), ?_⟩
      have : algebraMap T.V T.Fr (u⁻¹ : T.Vˣ) * algebraMap T.V T.Fr u = 1 := by
        rw [← map_mul]; simp
      rw [ha] at this
      field_simp at this
      exact this
    · exfalso
      have hm : a ∈ Ideal.span {π} := by rw [← hπ.maximalIdeal_eq]; exact hu
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 hm
      have h3 : ‖k x⁻¹‖ < 1 := by
        rw [← ha, map_mul, map_mul, norm_mul]
        calc _ ≤ ‖k (algebraMap T.V T.Fr π)‖ * 1 := mul_le_mul_of_nonneg_left (h1 b) (norm_nonneg _)
          _ < 1 := by simpa using hlt
      rw [map_inv₀, norm_inv] at h3
      have hp' : 0 < ‖k x‖ := norm_pos_iff.2 ((map_ne_zero k).2 h0)
      have := (inv_lt_one₀ hp').1 h3
      linarith

theorem exists_log_norm {C : Type} [NormedField C] (j : T.Fr →+* C)
    (hj : ∀ a : T.Fr, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap T.V T.Fr).range) :
    ∃ ρ : ℝ, ρ < 0 ∧ ∀ x : T.Fr, x ≠ 0 → Real.log ‖j x‖ = Formalism.L2.Pj.vV T.V x * ρ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have h1 : ∀ a : T.V, ‖j (algebraMap T.V T.Fr a)‖ ≤ 1 := fun a => (hj _).2 ⟨a, rfl⟩
  have hne : algebraMap T.V T.Fr π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hπ.ne_zero
  have hpos : 0 < ‖j (algebraMap T.V T.Fr π)‖ := norm_pos_iff.2 ((map_ne_zero j).2 hne)
  have hlt : ‖j (algebraMap T.V T.Fr π)‖ < 1 := by
    refine lt_of_le_of_ne (h1 π) fun he => ?_
    have : ‖j (algebraMap T.V T.Fr π)⁻¹‖ ≤ 1 := by rw [map_inv₀, norm_inv, he, inv_one]
    obtain ⟨b, hb⟩ := (hj _).1 this
    refine hπ.not_isUnit (IsUnit.of_mul_eq_one b ?_)
    apply IsFractionRing.injective T.V T.Fr
    rw [map_mul, hb, map_one, mul_inv_cancel₀ hne]
  refine ⟨Real.log ‖j (algebraMap T.V T.Fr π)‖, Real.log_neg hpos hlt, fun x hx => ?_⟩
  rw [norm_eq_zpow T j h1 hπ hx, Real.log_zpow]

end Values

section Pre

variable {S : Scheme.{0}} {A B G : Over S} [GrpObj G]

theorem pre_one (g : A ⟶ B) : g ≫ (1 : B ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (g ≫ toUnit B) (toUnit A)]

theorem pre_prod (g : A ⟶ B) {m : ℕ} (u : Fin m → (B ⟶ G)) :
    g ≫ (List.ofFn u).prod = (List.ofFn fun i => g ≫ u i).prod := by
  let f : (B ⟶ G) →* (A ⟶ G) :=
    { toFun := (g ≫ ·), map_one' := pre_one g, map_mul' := fun a b => by
        show g ≫ (a * b) = (g ≫ a) * (g ≫ b)
        rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift] }
  have := map_list_prod f (List.ofFn u)
  simpa [List.map_ofFn, f, Function.comp_def] using this

end Pre

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem mult_conj (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) : D.mult (ComplexEmbedding.conjugate τ) = D.q := by
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hd' : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h0 := H.sqrt_neg_disc_sq
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  simp [pow_two] at hre him
  have hr : H.rt0.re = 0 := by
    by_contra hne
    have h1 : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [h1] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  have hi : H.rt0.im ≠ 0 := by
    intro h1
    rw [hr, h1] at hre
    simp at hre
    exact H.d_prime.ne_zero hre
  unfold Datum.mult
  rw [if_neg]
  rw [ComplexEmbedding.conjugate_coe_eq, h]
  intro h2
  exact hi (by have := congrArg Complex.im h2; simp at this; linarith)

theorem exists_vecs {K : Type} [Field K] [Algebra c.F K] (z : Formalism.L2.Pj.FrPt Xo c K) {x : Sp K ⟶ Xo.X}
    (hx : x = z.x) (τ' : E →+* ℂ) {n : ℕ} (hn : D.mult τ' = n) :
    ∃ v : Fin n → (epsAt x ⟶ Xo.univ.t.G), ∀ i, (v i).left = z.u τ' (i.cast hn.symm) := by
  subst hx
  exact ⟨fun i => Over.homMk (z.u τ' (i.cast hn.symm)) (z.tan τ' _).1, fun i => rfl⟩

theorem isEigFrame_of_frPt {K : Type} [Field K] [Algebra c.F K] (z : Formalism.L2.Pj.FrPt Xo c K) {x : Sp K ⟶ Xo.X}
    (hx : x = z.x) (τ' : E →+* ℂ) {n : ℕ} (hn : D.mult τ' = n) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G))
    (hv : ∀ i, (v i).left = z.u τ' (i.cast hn.symm)) :
    IsEigFrame Xo.univ.t.act x ((algebraMap c.F K).comp (tauIn c τ')) v := by
  subst hx
  subst hn
  have hv' : ∀ i, (v i).left = z.u τ' i := fun i => by simpa using hv i
  refine ⟨fun i => ⟨?_, fun a => ?_⟩, fun w hw => ?_⟩
  · show _ ≫ (v i).left = _
    rw [hv']
    exact (z.tan τ' i).2
  · rw [Over.comp_left, hv']
    exact z.eig τ' i a
  · have hb := z.basis τ' w.left ⟨Over.w w, hw.1⟩ (fun a => hw.2 a)
    obtain ⟨a, ⟨u, hu1, hu2⟩, huniq⟩ := hb
    refine ⟨a, ⟨u, fun i => ?_, ?_⟩, fun b hb => huniq b ?_⟩
    · rw [hv']; exact hu1 i
    · exact Over.OverMorphism.ext hu2.symm
    · obtain ⟨u', h1, h2⟩ := hb
      exact ⟨u', fun i => by rw [h1 i, hv']; rfl, congrArg (·.left) h2.symm⟩

theorem exists_cast {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f g : S' ⟶ S} (h : f = g)
    (m : SABMap t' t f) : ∃ m' : SABMap t' t g, m'.φ = m.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem exists_lift_int (T : Formalism.L2.Pj.CDVR) (f : 𝓞 E →+* T.Fr) :
    ∃ σ : 𝓞 E →+* T.V, (algebraMap T.V T.Fr).comp σ = f := by
  have h : ∀ a, f a ∈ (algebraMap T.V T.Fr).range := fun a => by
    have hi : IsIntegral ℤ a := RingOfIntegers.isIntegral a
    have hV : IsIntegral T.V (f a) := by
      obtain ⟨q, hqm, hq⟩ := hi
      refine ⟨q.map (Int.castRingHom T.V), hqm.map _, ?_⟩
      rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap T.V T.Fr).comp (Int.castRingHom T.V))
        (f.comp (algebraMap ℤ (𝓞 E))), ← Polynomial.hom_eval₂, hq, map_zero]
    exact IsIntegrallyClosed.isIntegral_iff.1 hV
  let e : T.V ≃+* (algebraMap T.V T.Fr).range := RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
    ⟨fun a b hab => IsFractionRing.injective T.V T.Fr (congrArg Subtype.val hab),
      (algebraMap T.V T.Fr).rangeRestrict_surjective⟩
  refine ⟨(e.symm : _ →+* _).comp (f.codRestrict _ h), RingHom.ext fun a => ?_⟩
  have := e.apply_symm_apply (f.codRestrict _ h a)
  exact congrArg Subtype.val this

theorem eps_hom (V : Type) [CommRing V] : spMap (algebraMap V (DualNumber V)) ≫ 𝟙 (Sp V) =
    spMap ((algebraMap V (DualNumber V)).comp (algebraMap V V)) := by
  rw [Category.comp_id, Algebra.algebraMap_self, RingHom.comp_id]

theorem pt_hom (V : Type) [CommRing V] : spMap (algebraMap V V) = 𝟙 (Sp V) := by
  rw [Algebra.algebraMap_self]
  exact (congrArg Spec.map CommRingCat.ofHom_id).trans (Spec.map_id _)

def toAt (V : Type) [CommRing V] : epsOver V V ⟶ epsAt (𝟙 (Sp V)) :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans (eps_hom V))

def ofAt (V : Type) [CommRing V] : epsAt (𝟙 (Sp V)) ⟶ epsOver V V :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans (eps_hom V).symm)

theorem ofAt_toAt (V : Type) [CommRing V] : ofAt V ≫ toAt V = 𝟙 _ :=
  Over.OverMorphism.ext (Category.comp_id _)

def ptAt (V : Type) [CommRing V] : Over.mk (𝟙 (Sp V)) ⟶ ptOver V V :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans (pt_hom V))

theorem one_left_at (V : Type) [CommRing V] (G : Over (Sp V)) [GrpObj G] :
    (1 : Over.mk (𝟙 (Sp V)) ⟶ G).left = (1 : ptOver V V ⟶ G).left := by
  have h : ptAt V ≫ (1 : ptOver V V ⟶ G) = 1 := pre_one _
  rw [← h, Over.comp_left]
  exact Category.id_comp _

end Frames

end GlobalTheory.CompanionTheory.Ar.Flat.RuleVal
