import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumInvEqZeroOfUnramifiedCocycle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.QocEquiv
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.ZModInj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

namespace UpperTheory.V.ML.ReciprocityFromPoitouTateDuality

open GlobalTheory.Published GlobalTheory.Published.PoitouTate

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ}

private def Cob (l : ℕ) [Fact l.Prime] (r : ℕ) (A : ValuationSubring Ω) (w : G F Ω → G F Ω → ZMod (l ^ r)) : Prop :=
  ∃ b : Dec (F := F) A → ZMod (l ^ r), Continuous b ∧ ∀ g h : Dec (F := F) A,
    ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * b h - b (g * h) + b g = w g h

private theorem glob (hPT : PoitouTateDuality) (hl : l ≠ 2) (hr : 0 < r) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ContainsAbove S l) (Av : S → ValuationSubring Ω) (hA : ∀ v, IsPlaceOver (Av v) v.1)
    (w : G F Ω → G F Ω → ZMod (l ^ r)) (hc : Continuous fun p : G F Ω × G F Ω => w p.1 p.2)
    (hz : ∀ g h k, ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * w h k - w (g * h) k + w g (h * k) - w g h = 0)
    (hw : ∀ g h : G F Ω, ∀ u ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), ∀ u' ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))),
      w (g * u) (h * u') = w g h) (v₀ : S) (hv : ∀ v, v ≠ v₀ → Cob l r (Av v) w) : Cob l r (Av v₀) w := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_pow F Ω l r
  obtain ⟨inv, hinv, H⟩ := hPT F Ω l r (Or.inl hl) hr ζ hζ
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (Ω := Ω) (r := r) hS
  obtain ⟨W, hWc, hW⟩ := GlobalTheory.exists_descend_pair_quotient _ (fun p : G F Ω × G F Ω => w p.1 p.2) hc hw
  have e2 : ∀ g : G F Ω, μ (g : G F Ω ⧸ _) = cycMod F Ω l r g := fun g => DFunLike.congr_fun hμ g
  have hmem : W ∈ Z2 (charRep μ) := by
    refine ⟨hWc, fun g h k => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective h
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hW, hW, hW, hW, charRep_apply, e2]
    exact hz g h k
  have e := (H S hS Av hA μ hμ (ZMod (l ^ r)) (charRep μ) (contAction_charRep hμ)).1.sum_eq_zero
    (Submodule.Quotient.mk ⟨W, hmem⟩)
  have key : ∀ v : S, resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v)
      (Submodule.Quotient.mk ⟨W, hmem⟩) = 0 ↔ Cob l r (Av v) w := fun v => by
    refine (Submodule.Quotient.mk_eq_zero _).trans ((separated_dvr_second_cohomology_mem _ _).trans ?_)
    refine exists_congr fun b => and_congr_right fun _ => ?_
    rw [funext_iff, Prod.forall]
    refine forall_congr' fun g => forall_congr' fun h => ?_
    rw [← hW, ← e2]
    exact Iff.rfl
  rw [Finset.sum_eq_single v₀ (fun v _ h => by rw [(key v).2 (hv v h), map_zero])
    (fun h => (h (Finset.mem_univ _)).elim)] at e
  refine (key v₀).1 ((invAt_bijective S Av μ hμ hinv v₀ (hA v₀)).1 ?_)
  rw [e, map_zero]

private theorem cyc_ine {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v)
    (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) : cycMod F Ω l r σ = 1 := by
  refine Units.ext ?_
  have := cycZ_toZModPow_eq (l := l) hl hA (σ := σ) (q := 1) (fun x hx => by simpa using hσ.2 x hx) r
  rw [Nat.cast_one, map_one] at this
  exact this

private theorem loc (hU : UnramifiedOrthogonality) (hr : 0 < r) {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (f : Dec (F := F) A → ZMod (l ^ r)) (hf : Continuous f)
    (hz : ∀ g h, f (g * h) = f g + ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * f h)
    (H : ∀ x : Dec (F := F) A → ZMod (l ^ r), Continuous x → (∀ g h, x (g * h) = x g + x h) →
      (∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → x g = 0) →
      ∃ b : Dec (F := F) A → ZMod (l ^ r), Continuous b ∧ ∀ g h : Dec (F := F) A,
        ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * b h - b (g * h) + b g = f g * x h)
    (τ : Dec (F := F) A) (hτ : τ.1 ∈ Ine (F := F) A) : f τ = 0 := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let ρ : Representation (ZMod (l ^ r)) (Dec (F := F) A) (ZMod (l ^ r)) := 1
  let χ := (cycMod F Ω l r).comp (Dec (F := F) A).subtype
  have hc : ContAction ρ := continuous_snd
  have hU' : ∀ y : H1 (twDual χ ρ), y ∈ H1ur (twDual χ ρ) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) ↔
      ∀ x ∈ H1ur ρ ((Ine (F := F) A).subgroupOf (Dec (F := F) A)),
      cupH1H1TwistedDual χ ρ (MonoidHom.id _) (hc.comp' continuous_id) y x = 0 :=
    (hU F Ω l r (ZMod (l ^ r)) A ρ v hr hA hl (fun _ _ => rfl) hc).2
  let T : ZMod (l ^ r) → TDual (ZMod (l ^ r)) (ZMod (l ^ r)) := fun t => TDual.mk (LinearMap.mul _ _ t)
  have hT : ∀ t m, T t m = t * m := fun _ _ => rfl
  let y : Z1 (twDual χ ρ) := ⟨fun g => T (f g), (continuous_of_discreteTopology (f := T)).comp hf, fun g h => by
    ext m
    change f (g * h) * m = f g * m + twDual χ ρ g (T (f h)) m
    rw [twDual_apply, hz, add_mul, mul_assoc]
    rfl⟩
  have hy := (hU' (Submodule.Quotient.mk y)).2 fun x hx => by
    induction x using Submodule.Quotient.induction_on with | H x =>
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
    obtain ⟨b, hb, h⟩ := H x.1 x.2.1 x.2.2 fun g hg => (hm ⟨g, hg⟩).trans (sub_self _)
    exact (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨b, hb, funext fun p => h p.1 p.2⟩)
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hy)
  have h1 := congrArg (fun φ : TDual (ZMod (l ^ r)) (ZMod (l ^ r)) => φ 1) (hm ⟨τ, hτ⟩)
  change f τ * 1 = twDual χ ρ τ m 1 - m 1 at h1
  have h2 : χ τ = 1 := cyc_ine hA hl hτ
  rw [twDual_apply, h2, mul_one, Units.val_one, one_mul] at h1
  exact h1.trans (sub_self _)

private theorem gen {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) {φ : G F Ω}
    (hφ : IsFrob (F := F) A (normV v) φ) {B : Type} [AddCommGroup B] (d : Dec (F := F) A → B) (hd : IsLocallyConstant d)
    (hm : ∀ g h, d (g * h) = d g + d h) (hI : ∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → d g = 0)
    (h0 : d ⟨φ, hφ.1⟩ = 0) (g : Dec (F := F) A) : d g = 0 := by
  haveI : IsGalois F Ω := {}
  have h1 : d 1 = 0 := by simpa using hm 1 1
  let K : Subgroup (Dec (F := F) A) :=
    { carrier := {u | d u = 0}
      one_mem' := h1
      mul_mem' := fun {x y} hx hy => by
        change d _ = 0
        rw [hm, hx, hy, add_zero]
      inv_mem' := fun {x} hx => by
        have := hm x x⁻¹
        rw [mul_inv_cancel, h1, hx, zero_add] at this
        exact this.symm }
  have hK : IsClosed ((K.map (Dec (F := F) A).subtype : Subgroup (G F Ω)) : Set (G F Ω)) :=
    (isClosed_Dec A).isClosedMap_subtype_val _ (hd.isClosed_fiber 0)
  have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G F Ω) ⟨K.map (Dec (F := F) A).subtype, hK⟩
  have h2 : Dec (F := F) A ≤ K.map (Dec (F := F) A).subtype := by
    refine le_trans (le_sInf ?_) key.ge
    rintro N ⟨hNo, hN⟩
    exact Kum.decGen F Ω A v φ N hA hφ hNo
      (fun x hx => hN ⟨⟨x, Ine_le_Dec A hx⟩, hI _ hx, rfl⟩) (hN ⟨⟨φ, hφ.1⟩, h0, rfl⟩)
  obtain ⟨x, hx, e⟩ := h2 g.2
  rwa [← Subtype.ext e]

omit [NumberField F] [IsAlgClosure F Ω] in
private theorem coc_conj {Γ B : Type} [Group Γ] [CommRing B] {α : Γ →* B} {c : Γ → B}
    (hc : ∀ g h, c (g * h) = c g + α g * c h) : c 1 = 0 ∧ (∀ u, c u = 0 → c u⁻¹ = 0) ∧
      ∀ g u, α u = 1 → c u = 0 → c (g * u * g⁻¹) = 0 := by
  have h1 : c 1 = 0 := by simpa using hc 1 1
  refine ⟨h1, fun u hu => ?_, fun g u ha hu => ?_⟩
  · have := hc u⁻¹ u
    rw [inv_mul_cancel, h1, hu, mul_zero, add_zero] at this
    exact this.symm
  · rw [hc, hc, hu, map_mul, ha, mul_zero, add_zero, mul_one, ← hc, mul_inv_cancel, h1]

private theorem ns_le {B : Type} [CommRing B] (S : Set (HeightOneSpectrum (𝓞 F))) (φ : ZMod (l ^ r) →+* B)
    (α β : G F Ω →* B) (hαβ : ∀ g, α g * β g = φ ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)))
    (hα : IsLocallyConstant α) (c n : G F Ω → B) (hc : IsLocallyConstant c) (hn : IsLocallyConstant n)
    (cc : ∀ g h, c (g * h) = c g + α g * c h) (cn : ∀ g h, n (g * h) = n g + β g * n h)
    (hS : ∀ v ∉ S, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (h : ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ g ∈ Ine (F := F) A, α g = 1 ∧ c g = 0 ∧ n g = 0) :
    ∀ u ∈ NS Ω S, α u = 1 ∧ c u = 0 ∧ n u = 0 := by
  obtain ⟨c1, c2, c3⟩ := coc_conj cc
  obtain ⟨n1, n2, n3⟩ := coc_conj cn
  have hb : ∀ u, cycMod F Ω l r u = 1 → α u = 1 → β u = 1 := fun u h1 h2 => by
    have := hαβ u
    rwa [h1, h2, one_mul, Units.val_one, map_one] at this
  let K : Subgroup (G F Ω) :=
    { carrier := {u | cycMod F Ω l r u = 1 ∧ α u = 1 ∧ c u = 0 ∧ n u = 0}
      one_mem' := ⟨map_one _, map_one _, c1, n1⟩
      mul_mem' := fun {x y} hx hy => ⟨by rw [map_mul, hx.1, hy.1, mul_one], by rw [map_mul, hx.2.1, hy.2.1, mul_one],
        by rw [cc, hx.2.2.1, hy.2.2.1, mul_zero, add_zero], by rw [cn, hx.2.2.2, hy.2.2.2, mul_zero, add_zero]⟩
      inv_mem' := fun {x} hx => ⟨by rw [map_inv, hx.1, inv_one], by
        have := map_mul α x x⁻¹
        rw [mul_inv_cancel, map_one, hx.2.1, one_mul] at this
        exact this.symm, c2 _ hx.2.2.1, n2 _ hx.2.2.2⟩ }
  haveI : K.Normal := ⟨fun u hu g => ⟨by rw [map_mul, map_mul, hu.1, mul_one, ← map_mul, mul_inv_cancel, map_one],
    by rw [map_mul, map_mul, hu.2.1, mul_one, ← map_mul, mul_inv_cancel, map_one], c3 g u hu.2.1 hu.2.2.1,
    n3 g u (hb u hu.1 hu.2.1) hu.2.2.2⟩⟩
  have hcl : IsClosed (K : Set (G F Ω)) :=
    (isClosed_singleton.preimage continuous_cycMod).inter
      ((hα.isClosed_fiber 1).inter ((hc.isClosed_fiber 0).inter (hn.isClosed_fiber 0)))
  have hNS : NS Ω S ≤ K := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hcl
    intro g hg
    simp only [Set.mem_iUnion] at hg
    obtain ⟨v, hv, A, hA, hg⟩ := hg
    exact ⟨cyc_ine hA (hS v hv) hg, h v hv A hA g hg⟩
  exact fun u hu => (hNS hu).2

private theorem locq (hU : UnramifiedOrthogonality) (hr : 0 < r) {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) {B : Type} [CommRing B] (φ : ZMod (l ^ r) →+* B)
    (lam : B →+ ZMod (l ^ r)) (hlam : ∀ k z, lam (φ k * z) = k * lam z)
    (hχ : ∀ g ∈ Dec (F := F) A, φ ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) = 1)
    (c n : G F Ω → B) (hc : IsLocallyConstant c) (hn : IsLocallyConstant n)
    (cc : ∀ g h : Dec (F := F) A, c (g * h) = c g + c h) (cn : ∀ g h : Dec (F := F) A, n (g * h) = n g + n h)
    (hI : ∀ g ∈ Ine (F := F) A, c g = 0) (hb : ∃ b : Dec (F := F) A → ZMod (l ^ r), Continuous b ∧ ∀ g h : Dec (F := F) A,
        ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * b h - b (g * h) + b g = lam (n g * c h)) :
    ∀ g ∈ Dec (F := F) A, ∀ τ ∈ Ine (F := F) A, lam (n τ * c g) = 0 := by
  intro g hg τ hτ
  obtain ⟨b, hb, hb'⟩ := hb
  obtain ⟨σ, hσ⟩ := exists_isFrob (F := F) hA
  have hc' : IsLocallyConstant fun g : Dec (F := F) A => c g := hc.comp_continuous continuous_subtype_val
  have hn' : IsLocallyConstant fun g : Dec (F := F) A => n g := hn.comp_continuous continuous_subtype_val
  refine gen hA hσ (fun g => lam (n τ * c g)) (hc'.comp fun z => lam (n τ * z))
    (fun g h => by rw [← map_add, ← mul_add, ← cc]; rfl) (fun g hg => by rw [hI _ hg, mul_zero, map_zero]) ?_ ⟨g, hg⟩
  refine loc hU hr hA hl (fun g => lam (n g * c σ)) (hn'.comp fun z => lam (z * c σ)).continuous (fun g h => ?_)
    (fun x hx hm hxI => ?_) ⟨τ, Ine_le_Dec A hτ⟩ hτ
  · rw [← hlam, hχ _ g.2, one_mul, ← map_add, ← add_mul, ← cn]
    rfl
  · have hd := gen hA hσ (fun h => φ (x h) * c σ - φ (x ⟨σ, hσ.1⟩) * c h)
      ((((IsLocallyConstant.iff_continuous x).2 hx).comp fun z => φ z * c σ).sub
        (hc'.comp fun z => φ (x ⟨σ, hσ.1⟩) * z))
      (fun g h => by
        have e : c ((g * h : Dec (F := F) A) : G F Ω) = c g + c h := cc g h
        rw [hm, e, map_add]; ring)
      (fun g hg => by rw [hxI g hg, hI _ hg, map_zero, zero_mul, mul_zero, sub_zero]) (sub_self _)
    refine ⟨fun g => x ⟨σ, hσ.1⟩ * b g, continuous_const.mul hb, fun g h => ?_⟩
    have e : φ (x h) * (n g * c σ) = φ (x ⟨σ, hσ.1⟩) * (n g * c h) := by
      linear_combination n g * hd h
    have e2 := congrArg lam e
    rw [hlam, hlam] at e2
    linear_combination x ⟨σ, hσ.1⟩ * hb' g h - e2

omit [IsAlgClosure F Ω] in
private theorem over_iff {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hv : IsPlaceOver A v) (n : ℕ) :
    A.valuation (n : Ω) < 1 ↔ ((n : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have h := hv ((n : ℕ) : 𝓞 F)
  have e : algebraMap F Ω (((n : ℕ) : 𝓞 F) : F) = (n : Ω) := by simp
  rw [e] at h
  exact h

private theorem place_eq {q : ℕ} (hq : q.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)} (hv : (q : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  have h : Prime ((q : ℕ) : 𝓞 ℚ) := by
    have e : ((q : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((q : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.mp hq)
  have hm : (Ideal.span {((q : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime h.ne_zero).2 h).isMaximal (by simpa using h.ne_zero)
  exact HeightOneSpectrum.ext ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv)).symm.trans
    (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))

private theorem core (hPT : PoitouTateDuality) (hU : UnramifiedOrthogonality) {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (hl : l ≠ 2) (hr : 0 < r) {B : Type} [CommRing B] (φ : ZMod (l ^ r) →+* B)
    (lam : B →+ ZMod (l ^ r)) (hlam : ∀ k z, lam (φ k * z) = k * lam z)
    (α β : G ℚ Ω →* B) (hαβ : ∀ g, α g * β g = φ ((cycMod ℚ Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)))
    (hα : IsLocallyConstant α) {N q : ℕ} (hN : N ≠ 0) (hlN : l ∣ N) (hq : q.Prime) (hql : q ≠ l)
    (c n : G ℚ Ω → B) (hc : IsLocallyConstant c) (hn : IsLocallyConstant n)
    (cc : ∀ g h, c (g * h) = c g + α g * c h) (cn : ∀ g h, n (g * h) = n g + β g * n h)
    (hun : ∀ A : ValuationSubring Ω, ¬ Over A (N * q) → ∀ g ∈ Ine (F := ℚ) A, α g = 1 ∧ c g = 0 ∧ n g = 0)
    (hcob : ∀ A : ValuationSubring Ω, Over A N → ¬ Over A q → ∃ m : B, ∀ g ∈ Dec (F := ℚ) A, c g = α g * m - m)
    (A₀ : ValuationSubring Ω) (hA₀ : Over A₀ q) (htr : ∀ g ∈ Dec (F := ℚ) A₀, α g = 1 ∧ β g = 1)
    (hI : ∀ g ∈ Ine (F := ℚ) A₀, c g = 0) :
    ∀ g ∈ Dec (F := ℚ) A₀, ∀ τ ∈ Ine (F := ℚ) A₀, lam (n τ * c g) = 0 := by
  classical
  obtain ⟨-, -, hmul, hcop, -, -, -, -, hpl, -⟩ := placeBasic Ω
  obtain ⟨v₀, hv₀, -, hq₀⟩ := hpl A₀ q hq hA₀
  have hfin : {v : HeightOneSpectrum (𝓞 ℚ) | ((N * q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span {((N * q : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
      exact mul_ne_zero hN hq.ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
  let S := hfin.toFinset
  have hmem : ∀ v, v ∈ S ↔ ((N * q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := fun v => hfin.mem_toFinset
  have hlS : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S := fun v hv => by
    obtain ⟨k, rfl⟩ := hlN
    rw [hmem, Nat.cast_mul, Nat.cast_mul, mul_assoc]
    exact v.asIdeal.mul_mem_right _ hv
  have h₀ : v₀ ∈ S := by
    rw [hmem, Nat.cast_mul]
    exact v₀.asIdeal.mul_mem_left _ hq₀
  let Av : S → ValuationSubring Ω := fun v => if v.1 = v₀ then A₀ else placeOf Ω v.1
  have hAv : ∀ v, IsPlaceOver (Av v) v.1 := fun v => by
    by_cases h : v.1 = v₀
    · simp only [Av, if_pos h]
      rw [h]; exact hv₀
    · simp only [Av, if_neg h]
      exact isPlaceOver_placeOf Ω v.1
  have hA0 : Av ⟨v₀, h₀⟩ = A₀ := if_pos rfl
  have hχ : ∀ g z, ((cycMod ℚ Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * lam z = lam (α g * β g * z) := fun g z => by
    rw [hαβ, hlam]
  have hNS := ns_le (S : Set (HeightOneSpectrum (𝓞 ℚ))) φ α β hαβ hα c n hc hn cc cn (fun v hv h => hv (hlS v h))
    fun v hv A hA => hun A fun h => hv ((hmem v).2 ((over_iff hA _).1 h))
  have hG := glob hPT hl hr S hlS Av hAv (fun g h => lam (n g * (α g * c h)))
    (((hn.comp_continuous continuous_fst).mul ((hα.comp_continuous continuous_fst).mul
      (hc.comp_continuous continuous_snd))).comp lam).continuous
    (fun g h k => by
      rw [hχ, ← map_sub, ← map_add, ← map_sub, cn g h, cc h k, map_mul α, ← map_zero lam]
      congr 1
      ring)
    (fun g h u hu u' hu' => by
      rw [cn, map_mul α, cc, (hNS u hu).1, (hNS u hu).2.2, (hNS u' hu').2.1, mul_zero, mul_zero, add_zero, add_zero,
        mul_one])
    ⟨v₀, h₀⟩ fun v hv => by
      have h1 : ¬ Over (Av v) q := fun h => hv (Subtype.ext (place_eq hq ((over_iff (hAv v) _).1 h) hq₀))
      obtain ⟨m, hm⟩ := hcob (Av v) (((hmul _ _ _).1 ((over_iff (hAv v) _).2 ((hmem _).1 v.2))).resolve_right h1) h1
      refine ⟨fun g => -lam (n g * (α g * m)),
        (((hn.mul (hα.comp (· * m))).comp fun z => -lam z).comp_continuous continuous_subtype_val).continuous,
        fun g h => ?_⟩
      beta_reduce
      rw [mul_neg, hχ, ← map_neg, ← map_neg, ← map_neg, ← map_sub, ← map_add, hm h h.2, Subgroup.coe_mul, cn, map_mul α]
      congr 1
      ring
  rw [hA0] at hG
  obtain ⟨b, hb, hb'⟩ := hG
  refine locq hU hr hv₀ (fun h => hcop A₀ q l ((Nat.coprime_primes hq Fact.out).2 hql) hA₀ ((over_iff hv₀ _).2 h))
    φ lam hlam (fun g hg => by rw [← hαβ, (htr g hg).1, (htr g hg).2, one_mul]) c n hc hn
    (fun g h => by rw [cc, (htr g g.2).1, one_mul]) (fun g h => by rw [cn, (htr g g.2).2, one_mul]) hI
    ⟨b, hb, fun g h => (hb' g h).trans (by beta_reduce; rw [(htr g g.2).1, one_mul])⟩

end UpperTheory.V.ML.ReciprocityFromPoitouTateDuality

open UpperTheory.V.ML.ReciprocityFromPoitouTateDuality in
theorem UpperTheory.V.ML.recip :
    GlobalTheory.Published.PoitouTateDuality → UnramifiedOrthogonality → Rec := by
  intro hPT hU Ω _ _ _ l _ hl O _ _ _ _ _ α a ha w₀ hw hop N q hN hlN hq hql c n hc hn ac an hun hcob A₀ hA₀ htr hI
    g hg τ hτ y hy
  obtain ⟨r₀, hr₀⟩ := (qoFacts l O).2.1 w₀
  have hdvd : a ∣ ((l ^ (r₀ + 1) : ℕ) : O) := by
    rw [← hw, Nat.cast_smul_eq_nsmul, pow_succ', mul_smul, hr₀, smul_zero]
  generalize hr : r₀ + 1 = r at hdvd
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let B := O ⧸ Ideal.span {a}
  let mk : O →+* B := Ideal.Quotient.mk _
  have hmk : ∀ u v : O, mk u = mk v ↔ a ∣ u - v := fun u v => Ideal.Quotient.eq.trans Ideal.mem_span_singleton
  have hmk1 : ∀ u : O, a ∣ u - 1 → mk u = 1 := fun u h => (hmk u 1).2 h
  let ι : B →ₗ[O] QO l O := (Ideal.span {a}).liftQ (LinearMap.toSpanSingleton O _ w₀) fun u hu =>
    (hw u).2 (Ideal.mem_span_singleton.1 hu)
  have hι : ∀ u, ι (mk u) = u • w₀ := fun _ => rfl
  have hιm : ∀ u x, ι (mk u * x) = u • ι x := fun u x => map_smul ι u x
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ((hw u).1 hx))
  have hsur : ∀ w : QO l O, a • w = 0 → ∃ x, ι x = w := fun w h => by
    obtain ⟨u, rfl⟩ := (qoCyc l O).2.2.1 a w₀ ha hw w h
    exact ⟨mk u, rfl⟩
  choose c' hc' using fun g => hsur _ (ac g)
  choose n' hn' using fun g => hsur _ (an g)
  have hz : ((l ^ r : ℕ) : B) = 0 := by
    rw [← map_natCast mk, ← map_zero mk, hmk, sub_zero]
    exact hdvd
  let φ : ZMod (l ^ r) →+* B := ZMod.castHom (ringChar.dvd hz) B
  have hφ : ∀ x : ℤ_[l], mk (algebraMap ℤ_[l] O x) = φ (PadicInt.toZModPow r x) := fun x => by
    have h1 : x - ((PadicInt.toZModPow r x).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow r : ℤ_[l] →+* _) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
    have h2 := map_dvd (algebraMap ℤ_[l] O) h1
    rw [map_sub, map_natCast, map_pow, map_natCast, ← Nat.cast_pow] at h2
    rw [(hmk _ _).2 (hdvd.trans h2), map_natCast, ← map_natCast φ, ZMod.natCast_zmod_val]
  let α' : G ℚ Ω →* B := mk.toMonoidHom.comp ((Units.coeHom O).comp α)
  let β' : G ℚ Ω →* B := mk.toMonoidHom.comp ((Units.coeHom O).comp (dualChar l α))
  have hα' : ∀ g, α' g = mk (α g : O) := fun _ => rfl
  have hβ' : ∀ g, β' g = mk (dualChar l α g : O) := fun _ => rfl
  have hαβ : ∀ g, α' g * β' g = φ ((cycMod ℚ Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) := fun g => by
    have e : α g * dualChar l α g = chiO ℚ Ω l O g := by
      change α g * (chiO ℚ Ω l O g * (α g)⁻¹) = _
      rw [mul_comm, inv_mul_cancel_right]
    rw [hα', hβ', ← map_mul, ← Units.val_mul, e]
    exact hφ _
  have hlc : IsLocallyConstant α' := by
    rw [IsLocallyConstant.iff_exists_open]
    refine fun x => ⟨_, hop.preimage (continuous_const_mul x⁻¹), by simp, fun u hu => ?_⟩
    have h1 : α' (x⁻¹ * u) = 1 := hmk1 _ hu
    rw [← mul_inv_cancel_left x u, map_mul, h1, mul_one]
  have h0 : ∀ {x : B} {w : QO l O}, ι x = w → w = 0 → x = 0 := fun h1 h2 => hinj (by rw [h1, h2, map_zero])
  have hny : n' τ = mk y := hinj (by rw [hn', hy, hι])
  rw [← hc', ← hιm, ← hny]
  by_contra hne
  letI : Algebra (ZMod (l ^ r)) B := φ.toAlgebra
  obtain ⟨lam, -, hlam⟩ := KStar.Selmer.exists_form_ne_zero (N := l ^ r) (⊥ : Submodule (ZMod (l ^ r)) B)
    (z := n' τ * c' g) fun h => hne (by rw [(Submodule.mem_bot _).1 h, map_zero])
  refine hlam (core hPT hU hl (hr ▸ r₀.succ_pos) φ lam.toAddMonoidHom (fun k z => map_smul lam k z) α' β' hαβ hlc hN hlN
    hq hql c' n' (IsLocallyConstant.desc _ ι (by rw [show ι ∘ c' = c from funext hc']; exact hc.1) hinj)
    (IsLocallyConstant.desc _ ι (by rw [show ι ∘ n' = n from funext hn']; exact hn.1) hinj)
    (fun g h => hinj (by rw [map_add, hα', hιm, hc', hc', hc', hc.2]))
    (fun g h => hinj (by rw [map_add, hβ', hιm, hn', hn', hn', hn.2]))
    (fun A hA g hg => ⟨hmk1 _ (hun A hA g hg).1, h0 (hc' g) (hun A hA g hg).2.1, h0 (hn' g) (hun A hA g hg).2.2⟩)
    (fun A h1 h2 => ?_) A₀ hA₀ (fun g hg => ⟨hmk1 _ (htr g hg).1, hmk1 _ (htr g hg).2⟩)
    (fun g hg => h0 (hc' g) (hI g hg)) g hg τ hτ)
  obtain ⟨m, hm, h⟩ := hcob A h1 h2
  obtain ⟨m, rfl⟩ := hsur m hm
  exact ⟨m, fun g hg => hinj (by rw [map_sub, hα', hιm, hc', h g hg])⟩
