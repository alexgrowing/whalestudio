import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEmbeddingIdealLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR.Datum
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.PinCoord

theorem mk_sum_smul {O La : Type} [CommRing O] [AddCommGroup La] [Module O La] (J : Submodule O La) {r : ℕ}
    (c : Fin r → O) (x : Fin r → La) : (Submodule.Quotient.mk (∑ b, c b • x b) : La ⧸ J) =
      ∑ b, c b • (Submodule.Quotient.mk (x b) : La ⧸ J) := by
  change J.mkQ _ = _
  rw [map_sum]
  rfl

theorem isUnit_det_of_span : ∀ {O La ι : Type} [CommRing O] [AddCommGroup La] [Module O La] (P : Finset ι) (k : ι → Type) [∀ i, CommRing (k i)] (φ : ∀ i, O → k i) {r : ℕ} (ρ : ∀ i, Fin r → La →+ k i), (∀ i a c x, ρ i a (c • x) = φ i c * ρ i a x) → ∀ (J : Submodule O La), (∀ x, x ∈ J → ∀ i ∈ P, ∀ a, ρ i a x = 0) → (∀ t : ∀ i, Fin r → k i, ∃ x, ∀ i ∈ P, ∀ a, ρ i a x = t i a) → ∀ x : Fin r → La, Submodule.span O (Set.range fun b => (Submodule.Quotient.mk (x b) : La ⧸ J)) = ⊤ → ∀ i ∈ P, IsUnit (Matrix.of fun b a => ρ i a (x b)).det := by
  intro O La ι _ _ _ P k _ φ r ρ hs J hJ hon x hx i hi
  classical
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.vecMul_surjective_iff_isUnit]
  intro t
  obtain ⟨v, hv⟩ := hon (Pi.single i t)
  have hm : (Submodule.Quotient.mk v : La ⧸ J) ∈ Submodule.span O (Set.range fun b => (Submodule.Quotient.mk (x b) : La ⧸ J)) :=
    hx ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hm
  have hw : v - ∑ b, c b • x b ∈ J := by
    rw [← Submodule.Quotient.eq]
    rw [← hc]
    exact (mk_sum_smul J c x).symm
  refine ⟨fun b => φ i (c b), funext fun a => ?_⟩
  have h1 := hJ _ hw i hi a
  rw [map_sub, map_sum, sub_eq_zero] at h1
  simp only [hs] at h1
  have h2 := hv i hi a
  rw [Pi.single_eq_same] at h2
  rw [← h2, h1]
  simp [Matrix.vecMul, dotProduct]

theorem span_of_isUnit_det : ∀ {O La ι : Type} [CommRing O] [AddCommGroup La] [Module O La] (P : Finset ι) (k : ι → Type) [∀ i, CommRing (k i)] (φ : ∀ i, O → k i), (∀ t : ∀ i, k i, ∃ c, ∀ i ∈ P, φ i c = t i) → ∀ {r : ℕ} (ρ : ∀ i, Fin r → La →+ k i), (∀ i a c x, ρ i a (c • x) = φ i c * ρ i a x) → ∀ (J : Submodule O La), (∀ x, (∀ i ∈ P, ∀ a, ρ i a x = 0) → x ∈ J) → ∀ x : Fin r → La, (∀ i ∈ P, IsUnit (Matrix.of fun b a => ρ i a (x b)).det) → Submodule.span O (Set.range fun b => (Submodule.Quotient.mk (x b) : La ⧸ J)) = ⊤ := by
  intro O La ι _ _ _ P k _ φ hcrt r ρ hs J hJ x hu
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective J q
  have he : ∀ i, ∃ e : Fin r → k i, i ∈ P → Matrix.vecMul e (Matrix.of fun b a => ρ i a (x b)) = fun a => ρ i a v := by
    intro i
    by_cases hi : i ∈ P
    · have hs' := Matrix.vecMul_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (hu i hi))
      obtain ⟨e, he⟩ := hs' (fun a => ρ i a v)
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose e he using he
  choose c hc using fun b : Fin r => hcrt fun i => e i b
  have hmem : v - ∑ b, c b • x b ∈ J := hJ _ fun i hi a => by
    rw [map_sub, map_sum, sub_eq_zero]
    simp only [hs, hc _ i hi]
    have := congrFun (he i hi) a
    rw [← this]
    simp [Matrix.vecMul, dotProduct]
  have e1 : (Submodule.Quotient.mk v : La ⧸ J) = ∑ b, c b • (Submodule.Quotient.mk (x b) : La ⧸ J) := by
    rw [(Submodule.Quotient.eq J).2 hmem]
    exact mk_sum_smul J c x
  rw [e1]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem adjoint_comp_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (kst : LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d), (∀ u v : Dw.La, (d.pd : ℤ) ∣ Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H d.I • v) - Dw.EF u (cHalf H d.I • qRep (k (Submodule.Quotient.mk v)))) → ∀ f : Dw.La →ₗ[𝓞 E] Dw.La, (∀ x, (Submodule.Quotient.mk (f x) : LaI Xo c d) = k (Submodule.Quotient.mk x)) → (∀ x x', (d.pd : ℤ) ∣ Dw.EF (f x) (f x') - Dw.EF x x') → ∀ a : Dw.La, kst (Submodule.Quotient.mk (f a)) = (Submodule.Quotient.mk a : LaJ Xo c d) := by
  intro E _ _ _ H Dw l Xo c n d hd k kst hk f hf1 hf2 a
  obtain ⟨-, hM, -, hMb, hI, -⟩ := hd
  have hp := GlobalTheory.DatumInverseCharacter.half_prod hM hMb
  have hc := GlobalTheory.DatumInverseCharacter.cHalf_mem (H := H) d.I
  have hc1 := (GlobalTheory.HalfPairing.cHalf_spec (H := H) d.I hI).2
  have hN : d.pd ≠ 0 := by
    intro h
    have := d.l₂.three_le
    rw [hM, h] at this
    omega
  have hpd : (d.pd : 𝓞 E) ∈ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    have : Ideal.span {(d.pd : 𝓞 E)} ≤ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := hp ▸ Ideal.mul_le_right
    exact this (Ideal.subset_span rfl)
  rw [← GlobalTheory.HalfPairing.qRep_mk (kst (Submodule.Quotient.mk (f a))), Submodule.Quotient.eq]
  set z := qRep (kst (Submodule.Quotient.mk (f a) : LaJ Xo c d)) with hz
  set t := cHalf H d.I with ht
  have hdiv : ∀ v, (d.pd : ℤ) ∣ Dw.EF (z - a) (t • v) := by
    intro v
    have h1 := hk (f a) v
    have h2 := GlobalTheory.DatumInverseCharacter.dvd_right Dw hp hc (f a)
      (w := qRep (k (Submodule.Quotient.mk v)) - f v) (by
        rw [← Submodule.Quotient.eq, GlobalTheory.HalfPairing.qRep_mk, hf1])
    have h3 := hf2 a (t • v)
    rw [map_smul] at h3
    rw [smul_sub, map_sub] at h2
    have := dvd_add (dvd_add h1 h2) h3
    rw [map_sub, LinearMap.sub_apply]
    rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this
  have h4 : H.bar t • (z - a) ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) :=
    GlobalTheory.DatumInverseCharacter.mem_of_modN Dw hpd (GlobalTheory.DatumInverseCharacter.modN_of_dvd Dw (Nat.pos_of_ne_zero hN)
      fun q => by rw [Dw.adj, GlobalTheory.DatumInverseCharacter.bar_bar]; exact hdiv q)
  have h5 : (H.bar t - 1) • (z - a) ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) := by
    refine Submodule.smul_mem_smul ?_ trivial
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hc1
    rwa [map_sub, map_one] at this
  have := sub_mem h4 h5
  rwa [sub_smul, one_smul, sub_sub_cancel] at this

theorem topL_mul {κ : Type} [CommRing κ] {n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin n) (Fin r) κ) (B : Matrix (Fin r) (Fin r) κ) :
    topL r (A * B) = topL r A * B := by
  ext i j
  simp only [topL, Matrix.mul_apply, dif_pos (And.intro (lt_of_lt_of_le i.2 hrn) j.2), i.2, j.2, true_and,
    lt_of_lt_of_le i.2 hrn, Fin.is_lt, dite_true]

theorem topL_of {κ : Type} [Zero κ] {n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin n) (Fin r) κ) :
    topL r A = Matrix.of fun b a => A (Fin.castLE hrn b) a := by
  ext i j
  simp only [topL, dif_pos (And.intro (lt_of_lt_of_le i.2 hrn) j.2), Matrix.of_apply]
  rfl

theorem image_eq_range {α : Type} {n r : ℕ} (hrn : r ≤ n) (x : Fin n → α) :
    x '' {b | b.val < r} = Set.range fun a : Fin r => x (Fin.castLE hrn a) := by
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b.val, hb⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, a.2, rfl⟩

theorem exists_const_eq_inv_char : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (xJ : Fin n → LaJ Xo c d), d.PhiPin ph ψ xJ → ∀ (r : ℕ), Dw.p + Dw.q = r → r ≤ n → ∀ (Q : Finset (Pl E)) (ξ : ∀ P : Pl E, (kP P)ˣ →* ℂˣ) (ρ : ∀ P : Pl E, Fin r → Dw.La →+ kP P), (∀ (P : Pl E) (a : Fin r) (t : 𝓞 E) (x : Dw.La), ρ P a (t • x) = Ideal.Quotient.mk P.asIdeal (H.bar t) * ρ P a x) → (∀ x : Dw.La, x ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) ↔ ∀ P ∈ Q, ∀ a, ρ P a x = 0) → (∀ t : ∀ P : Pl E, Fin r → kP P, ∃ x, ∀ P ∈ Q, ∀ a, ρ P a x = t P a) → (∀ k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d, ∃ (f : Dw.La →ₗ[𝓞 E] Dw.La) (y : ∀ P : Pl E, GL (Fin r) (kP P)), (∀ x, (Submodule.Quotient.mk (f x) : LaI Xo c d) = k (Submodule.Quotient.mk x)) ∧ (∀ x x', (d.pd : ℤ) ∣ Dw.EF (f x) (f x') - Dw.EF x x') ∧ (∀ P ∈ Q, ∀ x : Fin n → Dw.La, (Matrix.of fun b a => ρ P a (x b)) = (Matrix.of fun b a => ρ P a (f (x b))) * (y P).val) ∧ (((ψ k : c.Fˣ) : c.F) : ℂ) = ∏ P ∈ Q, ((ξ P (Matrix.GeneralLinearGroup.det (y P)) : ℂˣ) : ℂ)) → ∃ u : ∀ P : Pl E, (kP P)ˣ, ∀ x : Fin n → Dw.La, (if h : ∀ P ∈ Q, IsUnit (topL r (Matrix.of fun b a => ρ P a (x b))).det then ∏ P ∈ Q.attach, (((ξ P.1 (h P.1 P.2).unit)⁻¹ : ℂˣ) : ℂ) else 0) = (∏ P ∈ Q, (((ξ P (u P))⁻¹ : ℂˣ) : ℂ)) * ((ph (fun b => Submodule.Quotient.mk (x b)) : c.F) : ℂ) := by
  intro E _ _ _ H Dw l Xo c n d hd ph ψ xJ hpin r hr hrn Q ξ ρ hs hker hon hfy
  subst hr
  obtain ⟨hc1, hc2, hc3, hc4, hc5, -⟩ := hpin
  obtain ⟨-, huniq, adj, -, hadj⟩ := GlobalTheory.HalfPairing.halves_free_and_adjoint E H Dw l Xo c n d hd
  have hcrt : ∀ t : ∀ P : Pl E, kP P, ∃ c, ∀ P ∈ Q, Ideal.Quotient.mk P.asIdeal (H.bar c) = t P := fun t => by
    obtain ⟨c, hc⟩ := GlobalTheory.BasePoint.crt_places Q t
    exact ⟨H.bar.symm c, fun P hP => by rw [RingEquiv.apply_symm_apply]; exact hc P hP⟩

  have hspan : ∀ x : Fin n → Dw.La, Submodule.span (𝓞 E) ((fun b => (Submodule.Quotient.mk (x b) : LaJ Xo c d)) ''
      {b | b.val < Dw.p + Dw.q}) = ⊤ ↔ ∀ P ∈ Q, IsUnit (topL (Dw.p + Dw.q) (Matrix.of fun b a => ρ P a (x b))).det := by
    intro x
    rw [image_eq_range hrn]
    simp only [topL_of hrn, Matrix.of_apply]
    exact ⟨isUnit_det_of_span Q (fun P => kP P) (fun P c => Ideal.Quotient.mk P.asIdeal (H.bar c)) ρ hs _
        (fun y hy => (hker y).1 hy) hon (fun a => x (Fin.castLE hrn a)),
      span_of_isUnit_det Q (fun P => kP P) (fun P c => Ideal.Quotient.mk P.asIdeal (H.bar c)) hcrt ρ hs _
        (fun y hy => (hker y).2 hy) (fun a => x (Fin.castLE hrn a))⟩
  set X₀ : Fin n → Dw.La := fun b => qRep (xJ b) with hX₀
  have hX₀mk : (fun b => (Submodule.Quotient.mk (X₀ b) : LaJ Xo c d)) = xJ :=
    funext fun b => GlobalTheory.HalfPairing.qRep_mk (xJ b)
  have hX₀u := (hspan X₀).1 (by rw [hX₀mk]; exact hc5)
  let u : ∀ P : Pl E, (kP P)ˣ := fun P =>
    if h : IsUnit (topL (Dw.p + Dw.q) (Matrix.of fun b a => ρ P a (X₀ b))).det then h.unit else 1
  have hu : ∀ P ∈ Q, ((u P : (kP P)ˣ) : kP P) = (topL (Dw.p + Dw.q) (Matrix.of fun b a => ρ P a (X₀ b))).det :=
    fun P hP => by simp only [u, dif_pos (hX₀u P hP), IsUnit.unit_spec]
  refine ⟨u, fun x => ?_⟩
  split_ifs with h
  ·
    have hxs := (hspan x).2 h
    rw [image_eq_range hrn] at hxs
    have hJs : Submodule.span (𝓞 E) (Set.range fun a : Fin (Dw.p + Dw.q) => xJ (Fin.castLE hrn a)) = ⊤ := by
      rw [← image_eq_range hrn]; exact hc5
    obtain ⟨kst, hkst, -⟩ := huniq _ _ hJs hxs
    have hk := (hadj (adj kst) kst).2 rfl
    have hph : ph (fun b => Submodule.Quotient.mk (x b)) = (((ψ (adj kst))⁻¹ : c.Fˣ) : c.F) := by
      have e1 : ph (fun b => Submodule.Quotient.mk (x b)) = ph (fun b => kst (xJ b)) :=
        hc1 _ _ fun b hb => (hkst ⟨b.val, hb⟩).symm
      rw [e1, hc3 (adj kst) kst hk xJ, hc4, mul_one]
    obtain ⟨f, y, hf1, hf2, hf3, hf4⟩ := hfy (adj kst)
    have hC := adjoint_comp_isometry E H Dw l Xo c n d hd (adj kst) kst hk f hf1 hf2
    have hfx : ∀ b : Fin n, b.val < Dw.p + Dw.q → ∀ P ∈ Q, ∀ a, ρ P a (f (x b)) = ρ P a (X₀ b) := by
      intro b hb P hP a
      have e2 : (Submodule.Quotient.mk (f (x b)) : LaJ Xo c d) = Submodule.Quotient.mk (X₀ b) := by
        apply kst.injective
        rw [hC, congrFun hX₀mk b]
        exact (hkst ⟨b.val, hb⟩).symm
      have := (hker (f (x b) - X₀ b)).1 ((Submodule.Quotient.eq _).1 e2) P hP a
      rwa [map_sub, sub_eq_zero] at this
    have hunit : ∀ (P : Pl E) (hP : P ∈ Q), (h P hP).unit = u P * Matrix.GeneralLinearGroup.det (y P) := by
      intro P hP
      apply Units.ext
      rw [IsUnit.unit_spec, Units.val_mul, hu P hP, Matrix.GeneralLinearGroup.val_det_apply, hf3 P hP x,
        topL_mul hrn, Matrix.det_mul]
      congr 2
      rw [topL_of hrn, topL_of hrn]
      ext b a
      exact hfx _ (by simp) P hP a
    have hL : ∏ P ∈ Q.attach, (((ξ P.1 (h P.1 P.2).unit)⁻¹ : ℂˣ) : ℂ) =
        (∏ P ∈ Q, (((ξ P (u P))⁻¹ : ℂˣ) : ℂ)) * (∏ P ∈ Q, ((ξ P (Matrix.GeneralLinearGroup.det (y P)) : ℂˣ) : ℂ))⁻¹ := by
      calc ∏ P ∈ Q.attach, (((ξ P.1 (h P.1 P.2).unit)⁻¹ : ℂˣ) : ℂ)
          = ∏ P ∈ Q.attach, ((((ξ P.1 (u P.1))⁻¹ : ℂˣ) : ℂ) *
              (((ξ P.1 (Matrix.GeneralLinearGroup.det (y P.1)) : ℂˣ) : ℂ))⁻¹) :=
            Finset.prod_congr rfl fun P _ => by
              rw [hunit P.1 P.2, map_mul, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val (ξ P.1 (Matrix.GeneralLinearGroup.det (y P.1)))]
        _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib,
            Finset.prod_attach Q (fun P => (((ξ P (u P))⁻¹ : ℂˣ) : ℂ)),
            Finset.prod_attach Q (fun P => ((ξ P (Matrix.GeneralLinearGroup.det (y P)) : ℂˣ) : ℂ))]
    rw [hL, ← hf4, hph, Units.val_inv_eq_inv_val, IntermediateField.coe_inv]
  ·
    have h0 : ph (fun b => Submodule.Quotient.mk (x b)) = 0 := by
      by_contra hne
      exact h ((hspan x).1 (hc2 _ hne))
    rw [h0]
    simp

end GlobalTheory.PinCoord

end
