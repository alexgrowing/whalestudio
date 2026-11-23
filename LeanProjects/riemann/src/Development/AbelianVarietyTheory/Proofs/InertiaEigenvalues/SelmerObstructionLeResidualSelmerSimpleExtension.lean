import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLCoeffMapFunctorial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLSaturatedOfSelmerSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerFunctorLeftExactTorsionCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepOnEqOfEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalEulerChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptySubquotEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H0TwDualEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelAllLeInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfComm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDegreeSum

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.SelObstruction

open GlobalTheory.SelLeftExact

section Linear

variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]

theorem card_quot_le (N : Submodule R X) {Y : Type} [Finite Y] (f : X → Y) (hf : ∀ x x', f x = f x' → x - x' ∈ N) :
    Finite (X ⧸ N) ∧ Nat.card (X ⧸ N) ≤ Nat.card Y := by
  choose s hs using Submodule.Quotient.mk_surjective N
  have hinj : Function.Injective (f ∘ s) := fun a b h => by
    rw [← hs a, ← hs b]
    exact (Submodule.Quotient.eq N).2 (hf _ _ h)
  exact ⟨Finite.of_injective _ hinj, Nat.card_le_card_of_injective _ hinj⟩

theorem card_eq_ker_mul_range {P : Type} [AddCommGroup P] [Module R P] (r : X →ₗ[R] P) :
    Nat.card X = Nat.card (LinearMap.ker r) * Nat.card (LinearMap.range r) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker r), Nat.card_congr r.quotKerEquivRange.toEquiv]

theorem card_comap_mul {P : Type} [AddCommGroup P] [Module R P] (r : X →ₗ[R] P) (L : Submodule R P) :
    Nat.card (L.comap r) * Nat.card P =
      Nat.card X * Nat.card L * Nat.card ((P ⧸ L) ⧸ LinearMap.range (L.mkQ ∘ₗ r)) := by
  have h1 := card_eq_ker_mul_range (L.mkQ ∘ₗ r)
  rw [LinearMap.ker_comp, Submodule.ker_mkQ] at h1
  rw [h1, Submodule.card_eq_card_quotient_mul_card L,
    Submodule.card_eq_card_quotient_mul_card (LinearMap.range (L.mkQ ∘ₗ r))]
  ring

end Linear

section Conn

variable {R Γ M' M M'' : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
  [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  [AddCommGroup M''] [Module R M''] [TopologicalSpace M''] [DiscreteTopology M'']
  (ρ' : Representation R Γ M') (ρ : Representation R Γ M) (ρ'' : Representation R Γ M'')
  (u : M' →ₗ[R] M) (w : M →ₗ[R] M'')

def IsConn (x : H1 ρ'') (k : H2 ρ') : Prop :=
  ∃ (z : Z1 ρ'') (c : Γ → M) (t : Z2 ρ'), Continuous c ∧ Submodule.Quotient.mk z = x ∧ (∀ g, w (c g) = z.1 g) ∧
    (∀ p, u (t.1 p) = d1 ρ c p) ∧ Submodule.Quotient.mk t = k

variable {ρ' ρ ρ'' u w}

theorem IsConn.sub {x x' : H1 ρ''} {k k' : H2 ρ'} (h : IsConn ρ' ρ ρ'' u w x k) (h' : IsConn ρ' ρ ρ'' u w x' k') :
    IsConn ρ' ρ ρ'' u w (x - x') (k - k') := by
  obtain ⟨z, c, t, hc, rfl, h1, h2, rfl⟩ := h
  obtain ⟨z', c', t', hc', rfl, h1', h2', rfl⟩ := h'
  refine ⟨z - z', c - c', t - t', hc.sub hc', rfl, fun g => ?_, fun p => ?_, rfl⟩
  · change w (c g - c' g) = z.1 g - z'.1 g
    rw [map_sub, h1, h1']
  · change u (t.1 p - t'.1 p) = _
    rw [map_sub, map_sub, h2, h2']
    rfl

theorem IsConn.res {x : H1 ρ''} {k : H2 ρ'} (h : IsConn ρ' ρ ρ'' u w x k) {D : Type} [Group D] [TopologicalSpace D]
    (φ : D →* Γ) (hφ : Continuous φ) :
    IsConn (ρ'.comp φ) (ρ.comp φ) (ρ''.comp φ) u w (resH1 ρ'' φ hφ x) (resH2 ρ' φ hφ k) := by
  obtain ⟨z, c, t, hc, rfl, h1, h2, rfl⟩ := h
  refine ⟨restrictCocycles1 ρ'' φ hφ z, c ∘ φ, restrictCocycles2 ρ' φ hφ t, hc.comp hφ, rfl, fun g => h1 _, fun p => ?_, rfl⟩
  refine (h2 (φ p.1, φ p.2)).trans ?_
  simp [d1]

variable (hu : ∀ g m, u (ρ' g m) = ρ g (u m)) (hw : ∀ g m, w (ρ g m) = ρ'' g (w m))
  (hinj : Function.Injective u) (hex : Function.Exact u w) (hsurj : Function.Surjective w) (hc : ContAction ρ)

include hu hw hinj hex hsurj hc in
theorem exists_isConn [ContinuousMul Γ] (x : H1 ρ'') : ∃ k, IsConn ρ' ρ ρ'' u w x k := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  choose s hs using hsurj
  have hcont : Continuous (s ∘ z.1) := (continuous_of_discreteTopology (f := s)).comp z.2.1
  have hZ : d1 ρ (s ∘ z.1) ∈ Z2 ρ := coboundaries2_le_cocycles2 ρ hc ⟨_, hcont, rfl⟩
  have h1 : ∀ p, u (Function.invFun u (d1 ρ (s ∘ z.1) p)) = d1 ρ (s ∘ z.1) p := fun p => by
    refine Function.invFun_eq ((hex _).1 ?_)
    obtain ⟨g, h⟩ := p
    simp only [d1_apply, map_add, map_sub, hw, Function.comp_apply, hs, z.2.2 g h]
    abel
  refine ⟨_, z, s ∘ z.1, ⟨fun p => Function.invFun u (d1 ρ (s ∘ z.1) p),
    (continuous_of_discreteTopology (f := Function.invFun u)).comp hZ.1, fun g h k => hinj ?_⟩, hcont, rfl,
    fun g => hs _, h1, rfl⟩
  rw [map_sub, map_add, map_sub, hu, h1, h1, h1, h1, map_zero]
  exact hZ.2 g h k

include hu hex in
theorem IsConn.lift {x : H1 ρ''} (h : IsConn ρ' ρ ρ'' u w x 0) :
    ∃ a, mapH1 ρ ρ'' w continuous_of_discreteTopology hw a = x := by
  obtain ⟨z, c, t, hc, rfl, h1, h2, h3⟩ := h
  obtain ⟨c', hc', e⟩ := (separated_dvr_second_cohomology_mem ρ' t.1).1 ((Submodule.Quotient.mk_eq_zero ((B2 ρ').comap (Z2 ρ').subtype)).1 h3)
  refine ⟨Submodule.Quotient.mk ⟨fun g => c g - u (c' g),
    hc.sub ((continuous_of_discreteTopology (f := u)).comp hc'), fun g h => ?_⟩, ?_⟩
  · have e1 := h2 (g, h)
    have e2 : t.1 (g, h) = _ := (congrFun e (g, h)).symm
    rw [e2, d1_apply, d1_apply, map_add, map_sub, hu] at e1
    change c (g * h) - u (c' (g * h)) = c g - u (c' g) + ρ g (c h - u (c' h))
    rw [map_sub]
    rw [← sub_eq_zero] at e1 ⊢
    rw [← e1]
    abel
  · refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
    change w (c g - u (c' g)) = _
    rw [map_sub, hex.apply_apply_eq_zero, sub_zero, h1]

include hu hinj hex hsurj hc in
theorem IsConn.eq_zero {a : H1 ρ} {k : H2 ρ'}
    (h : IsConn ρ' ρ ρ'' u w (mapH1 ρ ρ'' w continuous_of_discreteTopology hw a) k) : k = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨z, c, t, hcc, h0, h1, h2, rfl⟩ := h
  obtain ⟨m, hm⟩ := (mk_eq_zero_iff ρ'' (z - cocycles1MapOfEquivariant ρ ρ'' w continuous_of_discreteTopology hw a)).1
    (by rw [Submodule.Quotient.mk_sub, h0, sub_eq_zero]; rfl)
  obtain ⟨m, rfl⟩ := hsurj m
  have hb : d0 ρ m ∈ Z1 ρ := coboundaries_le_cocycles ρ hc ⟨m, rfl⟩
  have h3 : ∀ g, u (Function.invFun u (c g - a.1 g - d0 ρ m g)) = c g - a.1 g - d0 ρ m g := fun g => by
    refine Function.invFun_eq ((hex _).1 ?_)
    rw [map_sub, map_sub, amitsur_d0_apply, map_sub, hw, h1, sub_eq_zero]
    exact hm g
  refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem ρ' _).2 ⟨fun g => Function.invFun u (c g - a.1 g - d0 ρ m g),
    (continuous_of_discreteTopology (f := Function.invFun u)).comp ((hcc.sub a.2.1).sub hb.1), ?_⟩)
  funext ⟨g, h⟩
  refine hinj ?_
  change _ = u (t.1 (g, h))
  rw [h2, d1_apply, d1_apply, map_add, map_sub, hu, h3, h3, h3, a.2.2, hb.2, map_sub, map_sub]
  abel

variable {I : Type} {D : I → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i))

variable (ρ') in

def res1 : H1 ρ' →ₗ[R] ∀ i, H1 (ρ'.comp (φ i)) := LinearMap.pi fun i => resH1 ρ' (φ i) (hφ i)

variable (ρ') in

abbrev Cok (L' : LocCond ρ' φ) : Type :=
  ((∀ i, H1 (ρ'.comp (φ i))) ⧸ Submodule.pi Set.univ L') ⧸
    LinearMap.range ((Submodule.pi Set.univ L').mkQ ∘ₗ res1 ρ' φ hφ)

include hinj hex hsurj hc in

theorem exists_obstruction [ContinuousMul Γ] (L' : LocCond ρ' φ) (L : LocCond ρ φ) (L'' : LocCond ρ'' φ)
    (hL : ∀ i, ∀ x ∈ L' i, mapH1 (ρ'.comp (φ i)) (ρ.comp (φ i)) u continuous_of_discreteTopology
      (fun g m => hu (φ i g) m) x ∈ L i)
    (hL' : ∀ i, ∀ y ∈ L'' i, ∃ x ∈ L i, mapH1 (ρ.comp (φ i)) (ρ''.comp (φ i)) w continuous_of_discreteTopology
      (fun g m => hw (φ i g) m) x = y) :
    ∃ f : Sel ρ'' φ hφ L'' → Sha2 ρ' φ hφ × Cok ρ' φ hφ L', ∀ x x', f x = f x' →
      ∃ a ∈ Sel ρ φ hφ L, mapH1 ρ ρ'' w continuous_of_discreteTopology hw a = x.1 - x'.1 := by
  have hci : ∀ i, ContAction (ρ.comp (φ i)) := fun i => hc.comp (((hφ i).comp continuous_fst).prodMk continuous_snd)
  choose δ hδ using exists_isConn hu hw hinj hex hsurj hc
  have hδ0 : ∀ x : Sel ρ'' φ hφ L'', δ x.1 ∈ Sha2 ρ' φ hφ := fun x => (Submodule.mem_iInf _).2 fun i => by
    obtain ⟨y, -, hy⟩ := hL' i _ ((mem_Sel _ _ _ _ _).1 x.2 i)
    have := (hδ x.1).res (φ i) (hφ i)
    rw [← hy] at this
    exact this.eq_zero (fun g m => hu (φ i g) m) _ hinj hex hsurj (hci i)
  let δ' : Sel ρ'' φ hφ L'' → Sha2 ρ' φ hφ := fun x => ⟨_, hδ0 x⟩
  have key : ∀ x : Sel ρ'' φ hφ L'', ∃ (a : H1 ρ) (p : ∀ i, H1 (ρ'.comp (φ i))),
      mapH1 ρ ρ'' w continuous_of_discreteTopology hw a = x.1 - (Function.invFun δ' (δ' x)).1 ∧
      ∀ i, resH1 ρ (φ i) (hφ i) a - mapH1 (ρ'.comp (φ i)) (ρ.comp (φ i)) u continuous_of_discreteTopology
        (fun g m => hu (φ i g) m) (p i) ∈ L i := fun x => by
    have e : δ' (Function.invFun δ' (δ' x)) = δ' x := Function.invFun_eq ⟨x, rfl⟩
    have h1 := (hδ x.1).sub (hδ (Function.invFun δ' (δ' x)).1)
    rw [show δ (Function.invFun δ' (δ' x)).1 = δ x.1 from congrArg Subtype.val e, sub_self] at h1
    obtain ⟨a, ha⟩ := h1.lift hu hw hex
    have h2 : ∀ i, ∃ p, resH1 ρ (φ i) (hφ i) a - mapH1 (ρ'.comp (φ i)) (ρ.comp (φ i)) u continuous_of_discreteTopology
        (fun g m => hu (φ i g) m) p ∈ L i := fun i => by
      obtain ⟨y, hy, hy'⟩ := hL' i _ ((mem_Sel _ _ _ _ _).1 (x - Function.invFun δ' (δ' x)).2 i)
      obtain ⟨p, hp⟩ := exists_lift (ρ'.comp (φ i)) (ρ.comp (φ i)) (ρ''.comp (φ i)) u (fun g m => hu (φ i g) m) hinj w
        (fun g m => hw (φ i g) m) (fun m hm => (hex m).1 hm) (hci i)
        (fun m _ => (hsurj m).imp fun _ h => h.symm) (resH1 ρ (φ i) (hφ i) a - y) (by
          rw [map_sub, hy', ← selMaps_res_map, ha, sub_eq_zero]
          rfl)
      exact ⟨p, by rw [hp, sub_sub_cancel]; exact hy⟩
    choose p hp using h2
    exact ⟨a, p, ha, hp⟩
  choose a p ha hp using key
  refine ⟨fun x => (δ' x, Submodule.Quotient.mk (Submodule.Quotient.mk (p x))), fun x x' h => ?_⟩
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
  obtain ⟨b, hb⟩ := (Submodule.Quotient.eq _).1 h2
  have hb' : res1 ρ' φ hφ b - (p x - p x') ∈ Submodule.pi Set.univ L' := (Submodule.Quotient.eq _).1 hb
  refine ⟨a x - a x' - mapH1 ρ' ρ u continuous_of_discreteTopology hu b, (mem_Sel _ _ _ _ _).2 fun i => ?_, ?_⟩
  · have h3 := (L i).sub_mem ((L i).sub_mem (hp x i) (hp x' i)) (hL i _ (hb' i trivial))
    convert h3 using 1
    rw [map_sub, map_sub, selMaps_res_map, Pi.sub_apply, Pi.sub_apply, map_sub, map_sub, res1, LinearMap.pi_apply]
    abel
  · have h3 : mapH1 ρ ρ'' w continuous_of_discreteTopology hw
        (mapH1 ρ' ρ u continuous_of_discreteTopology hu b) = 0 := by
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      exact (mk_eq_zero_iff ρ'' _).2 ⟨0, fun g => by
        rw [map_zero, sub_zero]; exact hex.apply_apply_eq_zero _⟩
    rw [map_sub, map_sub, h3, ha, ha, show δ' x = δ' x' from h1]
    abel

theorem card_sel_of_euler [Fintype I] [∀ i, Finite (H1 (ρ.comp (φ i)))] (L : LocCond ρ φ) (m : ℕ)
    (hr : ∀ x : ∀ i, H2 (ρ.comp (φ i)), ∃ y, ∀ i, resH2 ρ (φ i) (hφ i) y = x i)
    (eG : Nat.card (H1 ρ) = Nat.card (H2 ρ) * m)
    (eP : ∏ i, Nat.card (H1 (ρ.comp (φ i))) =
      (∏ i, Nat.card (H0 (ρ.comp (φ i)))) * (∏ i, Nat.card (H2 (ρ.comp (φ i)))) * m ^ 2)
    (hL : ∏ i, Nat.card (L i) = (∏ i, Nat.card (H0 (ρ.comp (φ i)))) * m) :
    Finite (Cok ρ φ hφ L) ∧ Nat.card (Sel ρ φ hφ L) = Nat.card (Sha2 ρ φ hφ) * Nat.card (Cok ρ φ hφ L) := by
  haveI : Finite ((∀ v, H1 (ρ.comp (φ v))) ⧸ Submodule.pi Set.univ L) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  refine ⟨Finite.of_surjective _ (Submodule.Quotient.mk_surjective _), ?_⟩
  let r2 : H2 ρ →ₗ[R] ∀ v, H2 (ρ.comp (φ v)) := LinearMap.pi fun v => resH2 ρ (φ v) (hφ v)
  have hr2 : LinearMap.range r2 = ⊤ := LinearMap.range_eq_top.2 fun x => (hr x).imp fun _ h => funext h
  have e2 := card_eq_ker_mul_range r2
  rw [hr2, LinearMap.ker_pi, Nat.card_congr Submodule.topEquiv.toEquiv, Nat.card_pi] at e2
  have e1 := card_comap_mul (res1 ρ φ hφ) (Submodule.pi Set.univ L)
  have eS : (Submodule.pi Set.univ L).comap (res1 ρ φ hφ) = Sel ρ φ hφ L := by
    ext x
    rw [mem_Sel]
    exact ⟨fun h v => h v trivial, fun h v _ => h v⟩
  have eL : Nat.card (Submodule.pi Set.univ L) = ∏ v, Nat.card (L v) := by
    rw [← Nat.card_pi]
    exact Nat.card_congr ⟨fun x v => ⟨x.1 v, x.2 v trivial⟩, fun x => ⟨fun v => x v, fun v _ => (x v).2⟩,
      fun _ => rfl, fun _ => rfl⟩
  have hpos : 0 < Nat.card (∀ v, H1 (ρ.comp (φ v))) := Nat.card_pos
  have e2' : Nat.card (H2 ρ) = Nat.card (Sha2 ρ φ hφ) * ∏ v, Nat.card (H2 (ρ.comp (φ v))) := e2
  rw [eS, eL, hL, eG, e2'] at e1
  refine Nat.eq_of_mul_eq_mul_right hpos (e1.trans ?_)
  rw [Nat.card_pi, eP]
  ring

end Conn

section Count

variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime] {Λ M : Type} [CommRing Λ] [AddCommGroup M] [Module Λ M] [TopologicalSpace M] [DiscreteTopology M]
  (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω)

variable (F) in

abbrev Ab : Type := {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}

abbrev locAb (v : Ab F l) : Dec (F := F) (A.1 v.1) →* GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) := locHom _ (A.1 v.1)

omit [IsTotallyComplex F] [IsAlgClosure F Ω] [Fact l.Prime] in
theorem continuous_locAb (v : Ab F l) : Continuous (locAb l S A v) := continuous_locHom _ _

theorem card_sel (hPT : PoitouTateTotallyComplex) (hLF : LocalFiniteness) (hLE : LocalEulerChar)
    (hGF : GlobalFiniteness) (hGE : GlobalEulerChar) [Finite M] [Fintype (Ab F l)]
    (ρ : Representation Λ (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hl : ∀ m : M, l • m = 0)
    (hS : ContainsAbove S l) (hc : ContAction ρ) (h0 : H0 ρ = ⊥)
    (hd : ∀ (C : Type) [AddCommGroup C] (φ : M →+ C), (∀ g h m, φ (ρ g (ρ h m)) = φ (ρ h (ρ g m))) → φ = 0)
    (L : LocCond ρ (locAb l S A))
    (hL : ∏ v, Nat.card (L v) = (∏ v, Nat.card (H0 (ρ.comp (locAb l S A v)))) *
      Nat.card M ^ InfinitePlace.nrComplexPlaces F) :
    Finite (H1 ρ) ∧ Finite (Sha2 ρ (locAb l S A) (continuous_locAb l S A)) ∧
      Finite (Cok ρ (locAb l S A) (continuous_locAb l S A) L) ∧
      Nat.card (Sel ρ (locAb l S A) (continuous_locAb l S A) L) =
        Nat.card (Sha2 ρ (locAb l S A) (continuous_locAb l S A)) *
          Nat.card (Cok ρ (locAb l S A) (continuous_locAb l S A) L) := by
  classical
  obtain ⟨f1, f2, eG⟩ := GlobalTheory.EulerScalars.global_euler_char hGF hGE F Ω l Λ M S ρ hl hS hc
  have hloc := fun v : Ab F l => GlobalTheory.LocEulerScalars.localEulerChar_above hLF hLE F Ω l Λ M (A.1 v.1) v.1 (ρ.comp (locAb l S A v)) hl (A.2 v.1) v.2
    (hc.comp (((continuous_locAb l S A v).comp continuous_fst).prodMk continuous_snd))
  haveI := fun v => (hloc v).1
  refine ⟨f1, inferInstance, card_sel_of_euler _ _ L _ (fun x => ?_) ?_ ?_ hL⟩
  · obtain ⟨y, hy⟩ := GlobalTheory.LocTwoOnto.loc2_surjective hPT F Ω l Λ M S (fun v => A.1 v.1) ρ hl hS (fun v => A.2 v.1) hc hd
      fun v => if h : ((l : ℕ) : 𝓞 F) ∈ v.1.asIdeal then x ⟨v.1, h⟩ else 0
    exact ⟨y, fun v => (hy ⟨v.1, hS _ v.2⟩).trans (dif_pos v.2)⟩
  · rw [eG, h0, Nat.card_unique (α := (⊥ : Submodule Λ M)), one_mul]
  · rw [Finset.prod_congr rfl fun v _ => (hloc v).2.2, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, GlobalTheory.Proof.LocalDegreeSum.sum_locDeg F l, IsTotallyComplex.finrank, ← pow_mul, mul_comm 2]

end Count

section Transfer

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) {Λ M : Type} [CommRing Λ] [AddCommGroup M] [Module Λ M] [TopologicalSpace M] [DiscreteTopology M]

omit [IsAlgClosure F Ω] in
theorem ine_le_NS {S : Set (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    {A : ValuationSubring Ω} (hA : IsPlaceOver A v) : Ine (F := F) A ≤ NS Ω S := fun σ hσ => by
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, hσ⟩

omit [IsAlgClosure F Ω] in

theorem exists_descent (S : Set (HeightOneSpectrum (𝓞 F))) (ρ : Representation Λ (G F Ω) M) (hc : ContAction ρ)
    (h : ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := F) A, ∀ m, ρ σ m = m) :
    ∃ ρS : Representation Λ (GS Ω S) M, ContAction ρS ∧ ρS.comp (toGS Ω S) = ρ := by
  have hm : ∀ m, Continuous fun g => ρ g m := fun m => hc.comp (continuous_id.prodMk continuous_const)
  have hcl : IsClosed (ρ.ker : Set (G F Ω)) := by
    have : (ρ.ker : Set (G F Ω)) = ⋂ m, {g | ρ g m = m} := by
      ext g
      simp [LinearMap.ext_iff]
    rw [this]
    exact isClosed_iInter fun m => isClosed_eq (hm m) continuous_const
  have hle : NS Ω S ≤ ρ.ker := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun τ hτ => ?_) hcl
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, A, hA, hτ⟩ := hτ
    exact LinearMap.ext (h v hv A hA τ hτ)
  refine ⟨QuotientGroup.lift _ ρ hle, continuous_prod_of_discrete_right.2 fun m => ?_, rfl⟩
  exact (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (hm m)

variable {S : Finset (HeightOneSpectrum (𝓞 F))} (A : Formalism.GaloisCohomology.Places F Ω) {Sig : Set (HeightOneSpectrum (𝓞 F))}
  (hS : ∀ v, v ∈ S ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal ∨ v ∈ Sig)
  (ρ : Representation Λ (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
  (L : ∀ v, Submodule Λ (H1 ((ρ.comp (toGS Ω _)).comp (Dec (F := F) (A.1 v)).subtype)))

omit [IsAlgClosure F Ω] in
theorem inf_injective : Function.Injective (resH1 ρ (toGS Ω _) (continuous_toGS Ω _)) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, hm⟩ := (mk_eq_zero_iff _ (restrictCocycles1 ρ (toGS Ω _) (continuous_toGS Ω _) z)).1 hx
  refine (mk_eq_zero_iff ρ z).2 ⟨m, fun g => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  exact hm g

omit [IsAlgClosure F Ω] in
include hS in
theorem inf_mem_iff (x : H1 ρ) :
    resH1 ρ (toGS Ω _) (continuous_toGS Ω _) x ∈
        Formalism.GaloisCohomology.SelAll (ρ.comp (toGS Ω _)) A (Formalism.GaloisCohomology.bkCond (ρ.comp (toGS Ω _)) A l Sig L) ↔
      x ∈ Sel ρ (locAb l S A) (continuous_locAb l S A) fun v => L v.1 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine (mem_selAll_bkCond _ _ _ _ _ _).trans (Iff.trans ?_ (mem_Sel ρ (locAb l S A) (continuous_locAb l S A) _ _).symm)
  refine ⟨fun h v => h.1 v.1 v.2, fun h => ⟨fun v hv => h ⟨v, hv⟩, fun v hv hv' => ?_⟩⟩
  refine (mk_eq_zero_iff _ (restrictCocycles1 _ _ continuous_subtype_val (restrictCocycles1 _ _ continuous_subtype_val
    (restrictCocycles1 ρ (toGS Ω _) (continuous_toGS Ω _) z)))).2 ⟨0, fun g => ?_⟩
  have h1 : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) (g.1.1 : G F Ω) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (ine_le_NS (fun h => ((hS v).1 h).elim hv hv') (A.2 v) g.2)
  have h2 : z.1 1 = 0 := by
    have := z.2.2 1 1
    rw [one_mul, map_one] at this
    exact left_eq_add.1 this
  rw [map_zero, sub_zero, ← h2, ← h1]
  rfl

include hS in
theorem exists_inf (hc : ContAction ρ) (x : H1 (ρ.comp (toGS Ω _)))
    (hx : x ∈ Formalism.GaloisCohomology.SelAll (ρ.comp (toGS Ω _)) A (Formalism.GaloisCohomology.bkCond (ρ.comp (toGS Ω _)) A l Sig L)) :
    ∃ y : Sel ρ (locAb l S A) (continuous_locAb l S A) fun v => L v.1,
      resH1 ρ (toGS Ω _) (continuous_toGS Ω _) y.1 = x := by
  obtain ⟨y, rfl⟩ := GlobalTheory.SelInfl.selAllLeInf F Ω S Λ M ρ hc A _ (fun v hv => by
    unfold Formalism.GaloisCohomology.bkCond
    rw [if_neg fun h => hv ((hS v).2 (.inl h)), if_neg fun h => hv ((hS v).2 (.inr h))]) hx
  exact ⟨⟨y, (inf_mem_iff l A hS ρ L y).1 hx⟩, rfl⟩

end Transfer

section General

open Formalism.GaloisCohomology

variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime] {Λ M' M M'' : Type} [CommRing Λ]
  [AddCommGroup M'] [Module Λ M'] [TopologicalSpace M'] [DiscreteTopology M']
  [AddCommGroup M] [Module Λ M] [TopologicalSpace M] [DiscreteTopology M]
  [AddCommGroup M''] [Module Λ M''] [TopologicalSpace M''] [DiscreteTopology M'']

omit [IsTotallyComplex F] in
theorem finite_above : (placesOver F l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv

omit [IsTotallyComplex F] [Fact l.Prime] in
theorem finprod_above [Fintype (Ab F l)] (f : HeightOneSpectrum (𝓞 F) → ℕ) :
    ∏ᶠ v ∈ placesOver F l, f v = ∏ v : Ab F l, f v.1 := by
  rw [← finprod_eq_prod_of_fintype]
  exact (finprod_subtype_eq_finprod_cond _).symm

theorem obstruction_le (hPT : PoitouTateTotallyComplex) (hLF : LocalFiniteness) (hLE : LocalEulerChar)
    (hGF : GlobalFiniteness) (hGE : GlobalEulerChar) [Finite M'] (A : Places F Ω)
    (Sig : Set (HeightOneSpectrum (𝓞 F))) (hSig : Sig.Finite)
    (ρ' : Representation Λ (G F Ω) M') (ρ : Representation Λ (G F Ω) M) (ρ'' : Representation Λ (G F Ω) M'')
    (u : M' →ₗ[Λ] M) (w : M →ₗ[Λ] M'') (hu : ∀ g m, u (ρ' g m) = ρ g (u m)) (hw : ∀ g m, w (ρ g m) = ρ'' g (w m))
    (hinj : Function.Injective u) (hex : Function.Exact u w) (hsurj : Function.Surjective w)
    (hc' : ContAction ρ') (hc : ContAction ρ) (hc'' : ContAction ρ'')
    (hur : ∀ v, v ∉ placesOver F l → v ∉ Sig → ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B,
      ∀ m, ρ σ m = m)
    (hl : ∀ m : M', l • m = 0) (h0 : H0 ρ' = ⊥)
    (hd : ∀ (C : Type) [AddCommGroup C] (φ : M' →+ C), (∀ g h m, φ (ρ' g (ρ' h m)) = φ (ρ' h (ρ' g m))) → φ = 0)
    (L' : ∀ v, Submodule Λ (H1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)))
    (L : ∀ v, Submodule Λ (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype)))
    (L'' : ∀ v, Submodule Λ (H1 (ρ''.comp (Dec (F := F) (A.1 v)).subtype)))
    (hL : ∀ v, ∀ x ∈ L' v, mapH1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype) (ρ.comp (Dec (F := F) (A.1 v)).subtype) u
      continuous_of_discreteTopology (fun g m => hu g.1 m) x ∈ L v)
    (hL' : ∀ v, ∀ y ∈ L'' v, ∃ x ∈ L v, mapH1 (ρ.comp (Dec (F := F) (A.1 v)).subtype)
      (ρ''.comp (Dec (F := F) (A.1 v)).subtype) w continuous_of_discreteTopology (fun g m => hw g.1 m) x = y)
    (hcount : ∏ᶠ v ∈ placesOver F l, Nat.card (L' v) =
      (∏ᶠ v ∈ placesOver F l, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype))) *
        Nat.card M' ^ InfinitePlace.nrComplexPlaces F) :
    Finite (SelAll ρ' A (bkCond ρ' A l Sig L')) ∧
      Finite (↥(SelAll ρ'' A (bkCond ρ'' A l Sig L'')) ⧸ ((SelAll ρ A (bkCond ρ A l Sig L)).map
        (mapH1 ρ ρ'' w continuous_of_discreteTopology hw)).comap (SelAll ρ'' A (bkCond ρ'' A l Sig L'')).subtype) ∧
      Nat.card (↥(SelAll ρ'' A (bkCond ρ'' A l Sig L'')) ⧸ ((SelAll ρ A (bkCond ρ A l Sig L)).map
        (mapH1 ρ ρ'' w continuous_of_discreteTopology hw)).comap (SelAll ρ'' A (bkCond ρ'' A l Sig L'')).subtype) ≤
        Nat.card (SelAll ρ' A (bkCond ρ' A l Sig L')) := by
  haveI : Fintype (Ab F l) := (finite_above (F := F) l).fintype
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∈ S ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal ∨ v ∈ Sig :=
    ⟨((finite_above (F := F) l).union hSig).toFinset, fun v => Set.Finite.mem_toFinset _⟩
  have hur' : ∀ v ∉ (S : Set (HeightOneSpectrum (𝓞 F))), ∀ B : ValuationSubring Ω, IsPlaceOver B v →
      ∀ σ ∈ Ine (F := F) B, ∀ m, ρ σ m = m :=
    fun v hv => hur v (fun h => hv ((hS v).2 (.inl h))) fun h => hv ((hS v).2 (.inr h))
  obtain ⟨ρ', kc', rfl⟩ := exists_descent S ρ' hc' fun v hv B hB σ hσ m => hinj (by rw [hu, hur' v hv B hB σ hσ])
  obtain ⟨ρ'', kc'', rfl⟩ := exists_descent S ρ'' hc'' fun v hv B hB σ hσ m => by
    obtain ⟨m, rfl⟩ := hsurj m
    rw [← hw, hur' v hv B hB σ hσ]
  obtain ⟨ρ, kc, rfl⟩ := exists_descent S ρ hc hur'
  have hs : Function.Surjective (toGS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) := QuotientGroup.mk_surjective
  have huS : ∀ g m, u (ρ' g m) = ρ g (u m) := hs.forall.2 hu
  have hwS : ∀ g m, w (ρ g m) = ρ'' g (w m) := hs.forall.2 hw
  rw [finprod_above, finprod_above] at hcount
  obtain ⟨f1, f2, f3, e⟩ := card_sel l S A hPT hLF hLE hGF hGE ρ' hl (fun v hv => (hS v).2 (.inl hv)) kc'
    (eq_bot_iff.2 fun m hm => h0.le fun g => hm _)
    (fun C _ φ hφ => hd C φ fun g h m => hφ _ _ m) (fun v => L' v.1) hcount
  obtain ⟨f, hf⟩ := exists_obstruction huS hwS hinj hex hsurj kc (locAb l S A) (continuous_locAb l S A)
    (fun v => L' v.1) (fun v => L v.1) (fun v => L'' v.1) (fun v => hL v.1) (fun v => hL' v.1)
  have fin : Finite (SelAll (ρ'.comp (toGS Ω _)) A (bkCond (ρ'.comp (toGS Ω _)) A l Sig L')) := by
    choose s hs using exists_inf l A hS ρ' L' kc'
    exact Finite.of_injective (fun x => (s x.1 x.2).1) fun x y h =>
      Subtype.ext ((hs x.1 x.2).symm.trans ((congrArg _ h).trans (hs y.1 y.2)))
  choose s hs using exists_inf l A hS ρ'' L'' kc''
  obtain ⟨q1, q2⟩ := card_quot_le (((SelAll (ρ.comp (toGS Ω _)) A (bkCond (ρ.comp (toGS Ω _)) A l Sig L)).map
    (mapH1 _ _ w continuous_of_discreteTopology hw)).comap
      (SelAll (ρ''.comp (toGS Ω _)) A (bkCond (ρ''.comp (toGS Ω _)) A l Sig L'')).subtype)
    (fun x => f (s x.1 x.2)) fun x x' h => by
      obtain ⟨a, ha, ea⟩ := hf _ _ h
      refine ⟨_, (inf_mem_iff l A hS ρ L a).2 ha, ?_⟩
      refine (selMaps_res_map ρ ρ'' w continuous_of_discreteTopology hwS _ _ a).symm.trans ?_
      rw [ea, map_sub, hs, hs]
      rfl
  refine ⟨fin, q1, q2.trans ?_⟩
  rw [Nat.card_prod, ← e]
  exact Nat.card_le_card_of_injective (fun x => ⟨_, (inf_mem_iff l A hS ρ' L' x.1).2 x.2⟩) fun x y h =>
    Subtype.ext (inf_injective ρ' (congrArg Subtype.val h))

end General

section Main

open IsLocalRing

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i) {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ]
  [IsLocalHom (algebraMap (X.O0 i) Λ)] (κ : GE N →* Λˣ)

theorem bkOn_onto (htriv : TrivAbove κ (X.l i)) {B B'' : Type} [AddCommGroup B] [Module Λ B] [TopologicalSpace B]
    [DiscreteTopology B] [AddCommGroup B''] [Module Λ B''] [TopologicalSpace B''] [DiscreteTopology B'']
    (hB : Tors Λ B) (f : B →ₗ[Λ] B'') (hf : Function.Surjective f) (v : PlE D.host) :
    bkOn bkP i (Tgl i s) κ B'' v ≤ (bkOn bkP i (Tgl i s) κ B v).map (h1MapSubgroup (Tgl i s) κ (DecV N v) f) := by
  unfold bkOn
  split_ifs with hv
  · have hκ : ∀ g ∈ DecV N v, κ g = 1 := htriv v hv _ (N.plOm.2 v)
    refine Submodule.span_le.2 ?_
    rintro x ⟨w, c, y, b, hc, hcy, hw, rfl⟩
    obtain ⟨b, rfl⟩ := hf b
    have hy : y ∈ GlobalTheory.LocalSaturation.intCrys (bkP.br i v hv) (D.loc (X.l i)) (Tgl i s) := by
      change GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles.IsCrysCocycle _ _ _ _
      unfold GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles.IsCrysCocycle
      convert hc using 1
      funext g j
      rw [← hcy, MulEquiv.apply_symm_apply]
    refine ⟨Submodule.Quotient.mk ⟨_, GlobalTheory.LocalSaturation.smul_mem_Z1 _ _ _ κ B (X.twistBaseCoefficientRing_isAdic i) hB hκ hy b⟩,
      Submodule.subset_span ⟨_, c, y, b, hc, hcy, fun _ _ => rfl, rfl⟩, ?_⟩
    refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => funext fun a => ?_))
    exact (map_smul f _ _).trans (hw g a).symm
  · exact bot_le

omit [IsLocalHom (algebraMap (X.O0 i) Λ)] [Algebra (X.O0 i) Λ] in
theorem smul_eq_zero_of_simple {K : Type} [AddCommGroup K] [Module Λ K] (hK : IsSimpleModule Λ K) :
    ∀ x ∈ maximalIdeal Λ, ∀ k : K, x • k = 0 := fun x hx k => by
  have h := IsSimpleModule.annihilator_isMaximal (R := Λ) (M := K)
  rw [← eq_maximalIdeal h] at hx
  exact Module.mem_annihilator.1 hx k

theorem finite_of_simple [Module.Finite (X.O0 i) Λ] {K : Type} [AddCommGroup K] [Module Λ K]
    (hK : IsSimpleModule Λ K) : Finite K := by
  haveI := X.twistBaseCoefficientRing_residueField_finite i
  haveI : Module.Finite (ResidueField (X.O0 i)) (ResidueField Λ) := inferInstance
  haveI : Finite (ResidueField Λ) := Module.finite_of_finite (ResidueField (X.O0 i))
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hK
  rw [eq_maximalIdeal hI] at e
  exact Finite.of_equiv (ResidueField Λ) e.symm.toEquiv

theorem l_mem : ((X.l i : ℕ) : Λ) ∈ maximalIdeal Λ := by
  have h : ((X.l i : ℕ) : X.O0 i) ∈ maximalIdeal (X.O0 i) := by
    rw [← not_not (a := _ ∈ _), notMem_maximalIdeal]
    intro h
    have := h.map (algebraMap (X.O0 i) (X.O i))
    rw [map_natCast] at this
    exact notMem_maximalIdeal.2 this (X.O_l i)
  have := map_nonunit (algebraMap (X.O0 i) Λ) _ h
  rwa [map_natCast] at this

theorem finite_Spl : (Spl i).Finite := by
  refine Set.Finite.subset ((Set.finite_iUnion fun k => ?_).union (X.pD i).finite_toSet) Set.diff_subset
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  exact finite_above _

end Main

theorem selObs : PoitouTateTotallyComplex → CohDimTwo → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → NoInv i s κ → LocSat bkP i s κ → LocCount bkP i s κ → SelObs bkP i s κ Q := by
  intro hPT _ hLF _ hLE hGF hGE D N X bkP i s Λ _ _ _ κ Q h h0 _ hcount K B B'' _ _ _ _ _ _ _ _ _ _ _ _ hK hB f g hf hex hg
  obtain ⟨hG, hloc, hfin, hκ, -, htriv, -, hur⟩ := h
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI := finite_of_simple i hK
  have hkill := smul_eq_zero_of_simple hK
  have hKt : Tors Λ K := fun k => ⟨1, fun x hx => hkill x (by simpa using hx) k⟩
  have hB'' : Tors Λ B'' := fun b => by
    obtain ⟨b, rfl⟩ := hg b
    obtain ⟨n, hn⟩ := hB b
    exact ⟨n, fun x hx => by rw [← map_smul, hn x hx, map_zero]⟩
  have hcx : InfinitePlace.nrComplexPlaces D.host.E = D.R.f := by
    have h1 := IsTotallyComplex.finrank D.host.E
    have h2 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
      rw [D.host.finrank_cmField]
      unfold Ranks.f Ranks.n
      ring
    omega
  have hr : 100 ≤ D.R.r := hG.2.2.2.2.2.2
  refine obstruction_le (X.l i) hPT hLF hLE hGF hGE N.plOm (Spl i ∪ ↑Q) ((finite_Spl i).union Q.finite_toSet)
    (repOn (Tgl i s) κ K) (repOn (Tgl i s) κ B) (repOn (Tgl i s) κ B'') (f.compLeft _) (g.compLeft _)
    (repOn_map _ κ f) (repOn_map _ κ g) (fun x y e => funext fun a => hf (congrFun e a)) (fun x => ?_) (fun x => ?_)
    (contAction_of_tors (X.twistBaseCoefficientRing_isAdic i) _ (continuous_Tgl i s) κ hκ hKt)
    (contAction_of_tors (X.twistBaseCoefficientRing_isAdic i) _ (continuous_Tgl i s) κ hκ hB)
    (contAction_of_tors (X.twistBaseCoefficientRing_isAdic i) _ (continuous_Tgl i s) κ hκ hB'')
    (fun v hv hv' A hA σ hσ m => Colim.repOn_eq_of_eq_one _ κ
      (Colim.tgl_eq_one bkP i s hG.1 v hv (fun h => hv' (.inl h)) A hA σ hσ) (hur v (fun h => hv' (.inr h)) A hA σ hσ) m)
    (fun m => funext fun a => ?_) (h0 K hKt)
    (fun C _ φ hφ => GlobalTheory.ResComm.eq_zero_of_comm _ _ Λ K C _ (X.rhoS i s) (chiS i s) κ (by omega) hkill hG.2.1.1 φ hφ)
    (bkOn bkP i (Tgl i s) κ K) (bkOn bkP i (Tgl i s) κ B) (bkOn bkP i (Tgl i s) κ B'')
    (fun v x hx => localConditionAboveL_coeffMap_functorial bkP i _ κ f v x hx) (fun v y hy => bkOn_onto bkP i s κ htriv hB g hg v hy) ?_
  · refine ⟨fun e => ?_, ?_⟩
    · choose y hy using fun a => (hex (x a)).1 (congrFun e a)
      exact ⟨y, funext hy⟩
    · rintro ⟨y, rfl⟩
      exact funext fun a => hex.apply_apply_eq_zero _
  · choose y hy using fun a => hg (x a)
    exact ⟨y, funext hy⟩
  · rw [Pi.smul_apply, ← Nat.cast_smul_eq_nsmul Λ]
    exact hkill _ (l_mem i) _
  · rw [hcount K hK, hcx, Nat.card_pi, Finset.prod_const, Finset.card_fin, ← pow_mul, mul_comm D.R.r]

end GlobalTheory.SelObstruction
