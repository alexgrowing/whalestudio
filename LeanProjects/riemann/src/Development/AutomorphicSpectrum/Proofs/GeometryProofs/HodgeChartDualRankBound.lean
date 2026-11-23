import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateChartDualActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeCmTypeWeight
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure

open Module GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

section Abstract

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_std {R : Subalgebra o Ω} {T : Type} {x : T → Ω} : x ∈ stdLat R T ↔ ∀ k, x k ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem mem_mulLat {V : Type} [AddCommGroup V] [Module Ω V] {c : Ω} {L : AddSubgroup V} {x : V} :
    x ∈ mulLat c L ↔ ∃ y ∈ L, c • y = x := by
  simp [mulLat, AddSubgroup.mem_map]

theorem mem_dotDual {R : Subalgebra o Ω} {m : ℕ} {L : AddSubgroup (Fin m → Ω)} {z : Fin m → Ω} :
    z ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ z ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem seqHyp_of_mod (R : Subalgebra o Ω) {r s n : ℕ}
    {W : AddSubgroup (Fin r → Ω)} {om : AddSubgroup (Fin s → Ω)}
    {i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)} {q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)} {w u P : Ω}
    (hw : w ∈ R) (hu : u ∈ R) (hP : P = w * u)
    (hWs : ∀ t ∈ R, ∀ a ∈ W, t • a ∈ W) (hos : ∀ t ∈ R, ∀ z ∈ om, t • z ∈ om)
    (h1 : ∀ a ∈ W, i a ∈ stdLat R (Fin n)) (h2 : ∀ b ∈ stdLat R (Fin n), q b ∈ om)
    (Rt : (Fin n → Ω) →ₗ[Ω] (Fin r → Ω)) (hRt : ∀ x ∈ stdLat R (Fin n), Rt x ∈ W)
    (h3 : ∀ a ∈ W, ∃ a' ∈ W, Rt (i a) = a + P • a')
    (h4 : ∀ a ∈ W, ∃ y ∈ om, q (i a) = P • y)
    (h5 : ∀ b ∈ stdLat R (Fin n), ∀ y ∈ om, q b = P • y →
      ∃ a ∈ W, ∃ x ∈ stdLat R (Fin n), b = i a + P • x)
    (h6 : ∀ z ∈ om, ∃ b ∈ stdLat R (Fin n), ∃ y ∈ om, z = q b + P • y) :
    SeqHyp R w W om i q := by
  have hstd : ∀ t ∈ R, ∀ x ∈ stdLat R (Fin n), t • x ∈ stdLat R (Fin n) := fun t ht x hx =>
    mem_std.2 fun k => by simpa using R.mul_mem ht (mem_std.1 hx k)
  refine ⟨h1, h2, ?_, fun b hb => ⟨?_, ?_⟩, ?_⟩
  · intro a ha hia
    obtain ⟨x, hx, hxe⟩ := mem_mulLat.1 hia
    obtain ⟨a', ha', e⟩ := h3 a ha
    refine mem_mulLat.2 ⟨Rt x - u • a', W.sub_mem (hRt x hx) (hWs u hu a' ha'), ?_⟩
    have e1 : w • Rt x = a + P • a' := by rw [← map_smul, hxe, e]
    rw [smul_sub, e1, hP, smul_smul]
    abel
  · intro hq
    obtain ⟨y, hy, hye⟩ := mem_mulLat.1 hq
    obtain ⟨x₁, hx₁, y', hy', e⟩ := h6 y hy
    have e1 : q (b - w • x₁) = P • (w • y') := by
      rw [map_sub, map_smul, ← hye, e, hP]
      simp only [smul_add, smul_smul, add_sub_cancel_left]
      congr 1
      ring
    obtain ⟨a, ha, x, hx, e2⟩ := h5 _ ((stdLat R _).sub_mem hb (hstd w hw _ hx₁)) _ (hos w hw _ hy') e1
    refine ⟨a, ha, mem_mulLat.2 ⟨x₁ + u • x, (stdLat R _).add_mem hx₁ (hstd u hu _ hx), ?_⟩⟩
    rw [smul_add, smul_smul, ← hP]
    rw [sub_eq_iff_eq_add] at e2
    rw [e2]
    abel
  · rintro ⟨a, ha, hx⟩
    obtain ⟨x, hx, hxe⟩ := mem_mulLat.1 hx
    obtain ⟨y, hy, e⟩ := h4 a ha
    refine mem_mulLat.2 ⟨u • y + q x, om.add_mem (hos u hu _ hy) (h2 x hx), ?_⟩
    have e1 : b = i a + w • x := by rw [hxe]; abel
    rw [e1, map_add, map_smul, e, hP, smul_add, smul_smul]
  · intro z hz
    obtain ⟨b, hb, y, hy, e⟩ := h6 z hz
    refine ⟨b, hb, mem_mulLat.2 ⟨u • y, hos u hu _ hy, ?_⟩⟩
    rw [e, hP, smul_smul]
    abel

end Abstract

section Chart

variable {o Ω Li : Type} [CommRing o] [Field Ω] [Algebra o Ω] {R : Subalgebra o Ω}
  {E : Type} [Field E] [NumberField E] {c : E ≃+* E} {p Rr N : ℕ} [AddCommGroup Li] [Module Ω Li]
  (D : HTChart R Ω c p Rr N (Module.Dual Ω Li)) (ρ : 𝓞 E →+* Module.End Ω Li)

theorem mem_range_iff (x : Ω) : x ∈ (algebraMap R Ω).range ↔ x ∈ R :=
  ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem mem_lat {V : Submodule Ω Li} {e : Li} :
    e ∈ HTL.latOn D V (algebraMap R Ω 1) (algebraMap R Ω).range ↔ e ∈ V ∧ ∀ u ∈ D.om', u e ∈ R :=
  ⟨fun h => ⟨h.1, fun u hu => by simpa [mem_range_iff] using h.2 u hu⟩,
    fun h => ⟨h.1, fun u hu => by simpa [mem_range_iff] using h.2 u hu⟩⟩

theorem mem_lat' {V : Submodule Ω Li} {e : Li} :
    e ∈ HTL.latOn D V 1 (algebraMap R Ω).range ↔ e ∈ V ∧ ∀ u ∈ D.om', u e ∈ R :=
  ⟨fun h => ⟨h.1, fun u hu => by simpa [mem_range_iff] using h.2 u hu⟩,
    fun h => ⟨h.1, fun u hu => by simpa [mem_range_iff] using h.2 u hu⟩⟩

variable (hc : ∀ x, c (c x) = x)
  (hact : ∀ (a : 𝓞 E) (w : Module.Dual Ω Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))

include hc hact

theorem form_mem (σ : E →+* Ω) {e : Li} (he : e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom))
    (hl : ∀ u ∈ D.om', u e ∈ R) {f : Module.Dual Ω Li} (hf : f ∈ D.omHT σ) : f e ∈ R := by
  obtain ⟨u, hu, rfl⟩ := hf
  have : GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u e = u e := HTL.eigProj_apply D ρ hc hact σ he u
  change GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u e ∈ R
  rw [this]
  exact hl u hu

theorem eq_zero_of_forms [CharZero Ω] [Fact p.Prime] (σ : E →+* Ω) {e : Li} (he : e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom))
    (h : ∀ f ∈ D.omHT σ, f e = 0) : e = 0 := by
  have hp : ((p : Ω) ^ Rr) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have h1 : ∀ u ∈ D.om, u e = 0 := by
    intro u hu
    have hm : ((p : R) ^ Rr) • u ∈ D.om' :=
      Submodule.mem_sup_right ⟨u, hu, rfl⟩
    have h2 := h _ ⟨_, hm, rfl⟩
    have h3 : GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ (((p : R) ^ Rr) • u) e = (((p : R) ^ Rr) • u) e :=
      HTL.eigProj_apply D ρ hc hact σ he _
    have h4 : (((p : R) ^ Rr) • u) e = (p : Ω) ^ Rr * u e := by
      simp [Subalgebra.smul_def]
    have h5 : (p : Ω) ^ Rr * u e = 0 := by
      rw [← h4, ← h3]
      exact h2
    exact (mul_eq_zero.1 h5).resolve_left hp
  have h2 : ∀ u : Module.Dual Ω Li, u e = 0 := by
    intro u
    have hu : u ∈ Submodule.span Ω (D.om : Set (Module.Dual Ω Li)) := by
      rw [D.om_lat.span_eq_top]; trivial
    induction hu using Submodule.span_induction with
    | mem x hx => exact h1 x hx
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  exact (Module.forall_dual_apply_eq_zero_iff Ω e).1 h2

theorem form_eq_zero (σ : E →+* Ω) {f : Module.Dual Ω Li} (hf : f ∈ D.omHT σ)
    (h : ∀ e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom), f e = 0) : f = 0 := by
  obtain ⟨u, hu, rfl⟩ := hf
  change GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u = 0
  have hP : ∀ x : Li, eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ x ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom) := by
    intro x
    have h' := LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ x
    rw [LatBasic.mem_eigSp] at h' ⊢
    intro a
    have hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
      apply RingOfIntegers.ext
      simp [hc]
    have := h' (RingOfIntegers.mapRingEquiv c a)
    simpa [hinv] using this
  ext x
  have e1 : GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u x = u (GlobalTheory.CompanionTheory.Ar.HT.eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ x) := by
    rw [HTL.eigProj_dual D ρ hact, LinearMap.comp_apply]
  have e2 := HTL.eigProj_apply D ρ hc hact σ (hP x) u
  have e3 := h _ (hP x)
  change GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u _ = 0 at e3
  rw [e2] at e3
  rw [e1, e3]
  rfl

end Chart

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure

open Module GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

section Refl

variable {o Ω Li : Type} [CommRing o] [Field Ω] [Algebra o Ω] {R : Subalgebra o Ω}
  {E : Type} [Field E] [NumberField E] {c : E ≃+* E} {p Rr N : ℕ} [AddCommGroup Li] [Module Ω Li]
  (D : HTChart R Ω c p Rr N (Module.Dual Ω Li)) (ρ : 𝓞 E →+* Module.End Ω Li)
  (hc : ∀ x, c (c x) = x)
  (hact : ∀ (a : 𝓞 E) (w : Module.Dual Ω Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))

include hc hact

theorem exists_form [IsNoetherianRing R] [IsFractionRing R Ω] [CharZero Ω] [Fact p.Prime]
    (σ : E →+* Ω) (hproj : Module.Projective R (D.omHT σ)) {s : ℕ} (v' : Fin s → Li)
    (hv' : LinearIndependent Ω v')
    (hs : Submodule.span Ω (Set.range v') = GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom))
    (z : Fin s → Ω) (hz : ∀ l : Fin s → Ω, (∀ u ∈ D.om', u (∑ k, l k • v' k) ∈ R) → l ⬝ᵥ z ∈ R) :
    ∃ f ∈ D.omHT σ, ∀ k, f (v' k) = z k := by
  classical
  set V' := GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom) with hV'
  obtain ⟨ψ, hψk⟩ : ∃ ψ : Li →ₗ[Ω] Ω, ∀ k, ψ (v' k) = z k := by
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Basis.span hv').constr Ω z)
    refine ⟨g, fun k => ?_⟩
    have := congrArg (fun F => F (Basis.span hv' k)) hg
    simpa [Basis.span_apply, Basis.constr_basis, Finsupp.single_apply, ite_mul] using this
  have hψ : ∀ l : Fin s → Ω, ψ (∑ k, l k • v' k) = l ⬝ᵥ z := by
    intro l
    simp [map_sum, hψk, dotProduct]
  have hψR : ∀ e ∈ V', (∀ u ∈ D.om', u e ∈ R) → ψ e ∈ R := by
    intro e he hl
    obtain ⟨l, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 (hs ▸ he)
    rw [hψ]
    exact hz l hl
  have hle : D.om' ≤ D.om := by
    refine sup_le (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨x, rfl⟩
      exact D.h_mem x
    · rintro _ ⟨w, hw, rfl⟩
      exact D.om.smul_mem _ hw
  haveI hfin : Module.Finite R (D.omHT σ) :=
    Module.Finite.iff_fg.2 ((Submodule.FG.of_le D.om_lat.fg hle).map _)
  haveI := hproj
  have hvec : ∀ g : Module.Dual R (D.omHT σ), ∃ e ∈ V', ∀ y : D.omHT σ,
      (y : Module.Dual Ω Li) e = algebraMap R Ω (g y) :=
    fun g => HTL.exists_vec D ρ hc hact σ g
  choose ev hev hevg using hvec
  have hevL : ∀ g, ∀ u ∈ D.om', u (ev g) ∈ R := by
    intro g u hu
    have h1 := hevg g ⟨GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u, ⟨u, hu, rfl⟩⟩
    have h2 : GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u (ev g) = u (ev g) := HTL.eigProj_apply D ρ hc hact σ (hev g) u
    change GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u (ev g) = _ at h1
    rw [← h2, h1]
    exact (g _).2
  have huniq : ∀ e e', e ∈ V' → e' ∈ V' → (∀ y : D.omHT σ, (y : Module.Dual Ω Li) e = (y : Module.Dual Ω Li) e') → e = e' := by
    intro e e' he he' h
    have := eq_zero_of_forms D ρ hc hact σ (V'.sub_mem he he') (fun f hf => by
      rw [map_sub, h ⟨f, hf⟩, sub_self])
    exact sub_eq_zero.1 this
  let Φ : Module.Dual R (D.omHT σ) →ₗ[R] R :=
    { toFun := fun g => ⟨ψ (ev g), hψR _ (hev g) (hevL g)⟩
      map_add' := fun g g' => by
        apply Subtype.ext
        have : ev (g + g') = ev g + ev g' := huniq _ _ (hev _) (V'.add_mem (hev g) (hev g')) (fun y => by
          rw [map_add, hevg, hevg, hevg, LinearMap.add_apply, map_add])
        simp [this]
      map_smul' := fun a g => by
        apply Subtype.ext
        have : ev (a • g) = (a : Ω) • ev g := huniq _ _ (hev _) (V'.smul_mem _ (hev g)) (fun y => by
          rw [map_smul, hevg, hevg, LinearMap.smul_apply, smul_eq_mul, map_mul, smul_eq_mul]
          rfl)
        simp [this] }
  let f := (Module.evalEquiv R (D.omHT σ)).symm Φ
  have hf : ∀ g : Module.Dual R (D.omHT σ), g f = Φ g := fun g => by
    simpa [f] using Module.apply_evalEquiv_symm_apply (R := R) g Φ
  refine ⟨f, f.2, fun k => ?_⟩
  have key : ∀ e ∈ V', (∀ u ∈ D.om', u e ∈ R) → (f : Module.Dual Ω Li) e = ψ e := by
    intro e he hl
    let g : Module.Dual R (D.omHT σ) :=
      { toFun := fun y => ⟨(y : Module.Dual Ω Li) e, form_mem D ρ hc hact σ he hl y.2⟩
        map_add' := fun y y' => Subtype.ext (by simp)
        map_smul' := fun a y => Subtype.ext (by simp [Subalgebra.smul_def]) }
    have h1 : ev g = e := huniq _ _ (hev g) he (fun y => by rw [hevg]; rfl)
    have h2 := congrArg Subtype.val (hf g)
    change (f : Module.Dual Ω Li) e = ψ (ev g) at h2
    rw [h2, h1]
  have hloc : HTL.IsLocIn R (⊤ : Subring Ω) := by
    refine ⟨fun _ => trivial, fun b _ => ?_⟩
    obtain ⟨a, b', hb', rfl⟩ := IsFractionRing.div_surjective (A := R) b
    have h0 : algebraMap R Ω b' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb'
    exact ⟨b', a, h0, trivial, mul_div_cancel₀ _ h0⟩
  obtain ⟨t, ht0, -, ht⟩ := HTL.exists_unit_smul R Ω E c hc p Rr N Li D ρ hact V' 1 ⊤ hloc (v' k)
    ⟨hs ▸ Submodule.subset_span ⟨k, rfl⟩, fun _ _ => trivial⟩
  have h3 := key _ ht.1 (fun u hu => by simpa [mem_range_iff] using ht.2 u hu)
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, hψk] at h3
  exact mul_left_cancel₀ ht0 h3

end Refl

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure

open Module GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

theorem frame {Ω Li : Type} [Field Ω] [AddCommGroup Li] [Module Ω Li] {r : ℕ} {v : Fin r → Li}
    {V : Submodule Ω Li} (hv : LinearIndependent Ω v) (hs : Submodule.span Ω (Set.range v) = V) :
    (∀ a : Fin r → Ω, ∑ k, a k • v k ∈ V) ∧ (∀ e ∈ V, ∃ a : Fin r → Ω, ∑ k, a k • v k = e) ∧
      ∀ a b : Fin r → Ω, ∑ k, a k • v k = ∑ k, b k • v k → a = b := by
  refine ⟨fun a => hs ▸ Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩),
    fun e he => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hs ▸ he), fun a b h => ?_⟩
  have := Fintype.linearIndependent_iff.1 hv (a - b) (by simp [sub_smul, Finset.sum_sub_distrib, h])
  funext k
  exact sub_eq_zero.1 (this k)

theorem seqHyp_chart : ∀ (o Ω Li : Type) [CommRing o] [Field Ω] [CharZero Ω] [Algebra o Ω] (R : Subalgebra o Ω) [IsNoetherianRing R] [IsFractionRing R Ω] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (_ : ∀ x, c (c x) = x) (p Rr N r s m : ℕ) [Fact p.Prime] [AddCommGroup Li] [Module Ω Li] (D : HT.HTChart R Ω c p Rr N (Module.Dual Ω Li)) (ρ : 𝓞 E →+* Module.End Ω Li), (∀ (a : 𝓞 E) (w : Module.Dual Ω Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* Ω) (i₀ : Module.Dual R (D.omHT (σ.comp c.toRingHom)) →ₗ[R] (Fin N → R)), D.ExactMod σ m i₀ → D.IsDualMap σ 1 m i₀ → Module.Projective R (D.omHT σ) → ∀ (v : Fin r → Li) (v' : Fin s → Li), LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω v' → Submodule.span Ω (Set.range v') = HT.eigSp ρ (σ.comp c.toRingHom) → ∀ (W : AddSubgroup (Fin r → Ω)) (W' : AddSubgroup (Fin s → Ω)), (∀ a, a ∈ W ↔ ∀ u ∈ D.om', u (∑ k, a k • v k) ∈ R) → (∀ a, a ∈ W' ↔ ∀ u ∈ D.om', u (∑ k, a k • v' k) ∈ R) → ∀ w : Ω, w ∈ R → (∃ u ∈ R, (p : Ω) ^ m = w * u) → ∃ i : (Fin r → Ω) →ₗ[Ω] (Fin N → Ω), SeqHyp R w W (dotDual R W') i (Fintype.linearCombination Ω fun (n : Fin N) (k : Fin s) => D.h (Pi.single n 1) (v' k)) ∧ ∀ a ∈ W, ∀ j, ∃ z ∈ R, ∑ l, i a l * D.gram σ 1 l j = D.h (Pi.single j 1) (∑ k, a k • v k) + (p : Ω) ^ m * z := by
  intro o Ω Li _ _ _ _ R _ _ E _ _ c hc p Rr N r s m _ _ _ D ρ hact σ i₀ hex hdual hproj v v' hv hvs hv' hvs' W W'
    hW hW' w hwR hwu
  obtain ⟨u, huR, hwu⟩ := hwu
  classical
  have hσσ : (σ.comp c.toRingHom).comp c.toRingHom = σ := by
    ext x
    simp [hc]
  obtain ⟨J, Rr', hJ1, hJ2, hJ3⟩ := GlobalTheory.T.hodge_tate_chart_dual_action R Ω E c hc p Rr N Li D ρ hact σ 1 m i₀ (by simp) hex
  obtain ⟨hVv, hSv, hIv⟩ := frame hv hvs
  obtain ⟨hVv', hSv', hIv'⟩ := frame hv' hvs'
  have hLat : ∀ e, e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap R Ω 1) (algebraMap R Ω).range ↔
      e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ ∧ ∀ u ∈ D.om', u e ∈ R := fun e => mem_lat D
  have hWl : ∀ a, a ∈ W ↔ (∑ k, a k • v k) ∈
      HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap R Ω 1) (algebraMap R Ω).range := fun a => by
    rw [hLat, hW]
    exact ⟨fun h => ⟨hVv a, h⟩, fun h => h.2⟩
  have hE : ∀ k (x : Module.Dual Ω Li), GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ x (v' k) = x (v' k) := fun k x =>
    HTL.eigProj_apply D ρ hc hact σ (hvs' ▸ Submodule.subset_span ⟨k, rfl⟩) x
  have hEσ : ∀ e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ, ∀ x : Module.Dual Ω Li,
      GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ (σ.comp c.toRingHom) x e = x e :=
    fun e he x => HTL.eigProj_apply D ρ hc hact (σ.comp c.toRingHom) (by rwa [hσσ]) x
  set q := Fintype.linearCombination Ω fun (n : Fin N) (k : Fin s) => D.h (Pi.single n 1) (v' k) with hq
  have hqM : ∀ x : Fin N → R, D.q σ x ∈ D.omHT σ := fun x =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ⟨_, HTL.h_mem_om' D _, rfl⟩
  have hqc : ∀ (x : Fin N → R) k, D.q σ x (v' k) = q (fun n => (x n : Ω)) k := by
    intro x k
    simp [HTChart.q, hq, Fintype.linearCombination_apply, Finset.sum_apply, hE, Subalgebra.smul_def]
  have hcd : ∀ z, z ∈ dotDual R W' ↔ ∃ f ∈ D.omHT σ, ∀ k, f (v' k) = z k := by
    intro z
    constructor
    · intro hz
      exact exists_form D ρ hc hact σ hproj v' hv' hvs' z fun l hl => mem_dotDual.1 hz l ((hW' l).2 hl)
    · rintro ⟨f, hf, hfz⟩
      refine mem_dotDual.2 fun l hl => ?_
      have h1 : l ⬝ᵥ z = f (∑ k, l k • v' k) := by
        simp [dotProduct, map_sum, hfz, mul_comm]
      rw [h1]
      exact form_mem D ρ hc hact σ (hVv' l) ((hW' l).1 hl) hf
  have hci : ∀ f ∈ D.omHT σ, ∀ f' ∈ D.omHT σ, (∀ k, f (v' k) = f' (v' k)) → f = f' := by
    intro f hf f' hf' h
    refine sub_eq_zero.1 (form_eq_zero D ρ hc hact σ ((D.omHT σ).sub_mem hf hf') fun e he => ?_)
    obtain ⟨a, rfl⟩ := hSv' e he
    simp [map_sum, h]
  have hlift : ∀ b ∈ stdLat R (Fin N), ∃ b₀ : Fin N → R, (fun n => (b₀ n : Ω)) = b :=
    fun b hb => ⟨fun n => ⟨b n, mem_std.1 hb n⟩, rfl⟩
  let Lv := Fintype.linearCombination Ω v
  have hLv : ∀ a, Lv a = ∑ k, a k • v k := fun a => Fintype.linearCombination_apply Ω v a
  have hWs : ∀ t ∈ R, ∀ a ∈ W, t • a ∈ W := by
    intro t ht a ha
    refine (hW _).2 fun u' hu' => ?_
    have : ∑ k, (t • a) k • v k = t • ∑ k, a k • v k := by
      simp [Finset.smul_sum, smul_smul]
    rw [this, map_smul, smul_eq_mul]
    exact R.mul_mem ht ((hW a).1 ha u' hu')
  have hos : ∀ t ∈ R, ∀ z ∈ dotDual R W', t • z ∈ dotDual R W' := fun t ht z hz =>
    mem_dotDual.2 fun l hl => by
      rw [dotProduct_smul, smul_eq_mul]
      exact R.mul_mem ht (mem_dotDual.1 hz l hl)
  have hJf : ∀ a ∈ W, ∃ f : Module.Dual R (D.omHT (σ.comp c.toRingHom)),
      (∀ z : D.omHT (σ.comp c.toRingHom), algebraMap R Ω (f z) = (z : Module.Dual Ω Li) (∑ k, a k • v k)) ∧
        ∀ l, J (Lv a) l = algebraMap R Ω (i₀ f l) := by
    intro a ha
    obtain ⟨f, hf1, hf2⟩ := hJ1 _ ((hWl a).1 ha)
    exact ⟨f, fun z => by rw [hf1 z, map_one, _root_.one_mul], fun l => by rw [hLv]; exact hf2 l⟩
  have h1 : ∀ a ∈ W, (J ∘ₗ Lv) a ∈ stdLat R (Fin N) := by
    intro a ha
    obtain ⟨f, -, hf⟩ := hJf a ha
    exact mem_std.2 fun l => by rw [LinearMap.comp_apply, hf l]; exact (i₀ f l).2
  have hqd : ∀ x : Fin N → R, q (fun n => (x n : Ω)) ∈ dotDual R W' := fun x =>
    (hcd _).2 ⟨_, hqM x, fun k => hqc x k⟩
  have h2 : ∀ b ∈ stdLat R (Fin N), q b ∈ dotDual R W' := by
    intro b hb
    obtain ⟨b₀, rfl⟩ := hlift b hb
    exact hqd b₀
  have hak : ∀ n : Fin N, ∃ a ∈ W, Lv a = Rr' (Pi.single n 1) := by
    intro n
    have h := (hLat _).1 (hJ2 n)
    obtain ⟨a, ha⟩ := hSv _ h.1
    refine ⟨a, (hWl a).2 ?_, by rw [hLv, ha]⟩
    rw [ha]
    exact hJ2 n
  choose ak hakW hakL using hak
  let Rt : (Fin N → Ω) →ₗ[Ω] (Fin r → Ω) := Fintype.linearCombination Ω ak
  have hRtL : ∀ x, Lv (Rt x) = Rr' x := by
    intro x
    have hx : x = ∑ n, x n • Pi.single n (1 : Ω) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hx]
    simp only [Rt, Fintype.linearCombination_apply, map_sum, map_smul, hakL]
  have hRt : ∀ x ∈ stdLat R (Fin N), Rt x ∈ W := by
    intro x hx
    simp only [Rt, Fintype.linearCombination_apply]
    exact W.sum_mem fun n _ => hWs _ (mem_std.1 hx n) _ (hakW n)
  have h3 : ∀ a ∈ W, ∃ a' ∈ W, Rt ((J ∘ₗ Lv) a) = a + (p : Ω) ^ m • a' := by
    intro a ha
    obtain ⟨e', he', h⟩ := hJ3 _ ((hWl a).1 ha)
    obtain ⟨a', ha'⟩ := hSv _ ((hLat _).1 he').1
    refine ⟨a', (hWl a').2 (by rw [ha']; exact he'), hIv _ _ ?_⟩
    have e1 : Lv (Rt ((J ∘ₗ Lv) a)) = Lv (a + (p : Ω) ^ m • a') := by
      rw [hRtL, LinearMap.comp_apply, hLv a, h, map_add, map_smul, hLv, hLv, ha']
    rwa [hLv, hLv] at e1
  have h4 : ∀ a ∈ W, ∃ y ∈ dotDual R W', q ((J ∘ₗ Lv) a) = (p : Ω) ^ m • y := by
    intro a ha
    obtain ⟨f, -, hf⟩ := hJf a ha
    obtain ⟨y, hyM, hy⟩ := (hex.2.1 (i₀ f)).2 ⟨f, 0, by simp⟩
    refine ⟨fun k => y (v' k), (hcd _).2 ⟨y, hyM, fun _ => rfl⟩, ?_⟩
    have e1 : (J ∘ₗ Lv) a = fun n => ((i₀ f n : R) : Ω) := funext fun n => hf n
    rw [e1]
    funext k
    rw [← hqc (i₀ f) k, hy]
    simp [Subalgebra.smul_def]
  have h5 : ∀ b ∈ stdLat R (Fin N), ∀ y ∈ dotDual R W', q b = (p : Ω) ^ m • y →
      ∃ a ∈ W, ∃ x ∈ stdLat R (Fin N), b = (J ∘ₗ Lv) a + (p : Ω) ^ m • x := by
    intro b hb y hy hqy
    obtain ⟨b₀, rfl⟩ := hlift b hb
    obtain ⟨f, hfM, hfy⟩ := (hcd y).1 hy
    have e1 : D.q σ b₀ = ((p : R) ^ m) • f := hci _ (hqM b₀) _ ((D.omHT σ).smul_mem _ hfM) fun k => by
      rw [hqc, hqy]
      simp [Subalgebra.smul_def, hfy]
    obtain ⟨g, x', hgx⟩ := (hex.2.1 b₀).1 ⟨f, hfM, e1⟩
    obtain ⟨e, he, hge⟩ := HTL.exists_vec D ρ hc hact (σ.comp c.toRingHom) g
    rw [hσσ] at he
    have heL : e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap R Ω 1) (algebraMap R Ω).range := by
      refine (hLat e).2 ⟨he, fun u hu => ?_⟩
      have h' : GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ (σ.comp c.toRingHom) u e =
          algebraMap R Ω (g ⟨GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ (σ.comp c.toRingHom) u, ⟨u, hu, rfl⟩⟩) :=
        hge ⟨GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ (σ.comp c.toRingHom) u, ⟨u, hu, rfl⟩⟩
      rw [← hEσ e he u, h']
      exact (g _).2
    obtain ⟨a, rfl⟩ := hSv e he
    have ha : a ∈ W := (hWl a).2 heL
    obtain ⟨f₁, hf₁, hJf₁⟩ := hJf a ha
    have hfg : f₁ = g := LinearMap.ext fun z => Subtype.ext ((hf₁ z).trans (hge z))
    refine ⟨a, ha, fun n => (x' n : Ω), mem_std.2 fun n => (x' n).2, ?_⟩
    funext n
    have h6 := congrArg (fun x : R => (x : Ω)) (congrFun hgx n)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h6
    rw [Pi.add_apply, LinearMap.comp_apply, hJf₁ n, hfg]
    rw [h6]
    simp
  have h6 : ∀ z ∈ dotDual R W', ∃ b ∈ stdLat R (Fin N), ∃ y ∈ dotDual R W', z = q b + (p : Ω) ^ m • y := by
    intro z hz
    obtain ⟨f, hfM, hfz⟩ := (hcd z).1 hz
    obtain ⟨x, y', hy', e⟩ := hex.2.2 f hfM
    refine ⟨fun n => (x n : Ω), mem_std.2 fun n => (x n).2, fun k => y' (v' k),
      (hcd _).2 ⟨y', hy', fun _ => rfl⟩, ?_⟩
    funext k
    rw [← hfz k, e, LinearMap.add_apply, hqc]
    simp [Subalgebra.smul_def]
  refine ⟨J ∘ₗ Lv, seqHyp_of_mod R hwR huR hwu hWs hos h1 h2 Rt hRt h3 h4 h5 h6, ?_⟩
  intro a ha j
  obtain ⟨f, hf1, hf2⟩ := hJf a ha
  let y : D.omHT (σ.comp c.toRingHom) :=
    ⟨GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ (σ.comp c.toRingHom) (D.h (Pi.single j 1)), ⟨_, HTL.h_mem_om' D _, rfl⟩⟩
  obtain ⟨z, hz⟩ := hdual f j y rfl
  refine ⟨(z : Ω), z.2, ?_⟩
  have e1 : algebraMap R Ω (f y) = D.h (Pi.single j 1) (∑ k, a k • v k) := by
    rw [hf1 y]
    exact hEσ _ (hVv a) _
  simp only [LinearMap.comp_apply, hf2]
  rw [hz, map_add, e1, map_mul, map_pow, map_natCast]
  rfl

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure
