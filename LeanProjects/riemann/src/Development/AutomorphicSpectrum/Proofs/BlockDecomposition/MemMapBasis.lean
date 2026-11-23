import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemSpanOfEtale
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubSubSmulEqZeroOfSmulEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtendedDividedPowers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UZeroApplySelf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatCastIsUnit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLiftToThickening
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootExtensionLiftStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TowerNI

theorem twist {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) (hf : i.Flat) (g : D →+* D)
    (hgi : g.comp i = i) (χ w ξ μ : Λ) (hμ : μ = (χ - 1) * w * ξ) (hξ : IsNilpotent ξ)
    (hg : ∀ z, g z - z ∈ Ideal.span {i μ}) :
    (∀ x, i χ * g x = x → i μ * x = 0) ∧ ∀ 𝔞 : Ideal Λ, ∀ x ∈ 𝔞.map i,
      ∃ y ∈ (Ideal.span {ξ} * 𝔞).map i, i χ * g y - y = i μ * x := by
  letI : Algebra Λ D := i.toAlgebra
  haveI : Module.Flat Λ D := hf
  have hs : ∀ (a : Λ) (x : D), a • x = i a * x := fun a x => rfl
  have hgi' : ∀ a, g (i a) = i a := fun a => RingHom.congr_fun hgi a
  let γ : D →ₗ[Λ] D :=
    { toFun := fun x => i χ * g x
      map_add' := fun x y => by rw [map_add, mul_add]
      map_smul' := fun a x => by
        simp only [RingHom.id_apply, hs, map_mul, hgi']
        ring }
  have hγ : ∀ x, γ x = i χ * g x := fun _ => rfl
  have h : ∀ x, ∃ x', γ x - x - (χ - 1) • x = μ • x' := by
    intro x
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (hg x)
    refine ⟨i χ * y, ?_⟩
    rw [hγ, hs, hs, map_sub, map_one]
    linear_combination (- i χ) * hy
  obtain ⟨h1, h2⟩ := GlobalTheory.CompanionTheory.TwistedUnit.twisted_bijective_up_to γ (χ - 1) w ξ μ hμ hξ h
  refine ⟨fun x hx => h1 x hx, fun 𝔞 x hx => ?_⟩
  have hx' : x ∈ 𝔞 • (⊤ : Submodule Λ D) := by
    rw [Ideal.smul_top_eq_map]; exact hx
  obtain ⟨y, hy, e⟩ := h2 𝔞 x hx'
  rw [Ideal.smul_top_eq_map] at hy
  exact ⟨y, hy, e⟩

theorem mem_map_basis {D E ι : Type} [CommRing D] [CommRing E] [Algebra D E]
    (bb : Module.Basis ι D E) (𝔟 : Ideal D) (z : ι →₀ D) :
    bb.repr.symm z ∈ 𝔟.map (algebraMap D E) ↔ ∀ a, z a ∈ 𝔟 := by
  constructor
  · intro h a
    have h' : bb.repr.symm z ∈ 𝔟 • (⊤ : Submodule D E) := by
      rw [Ideal.smul_top_eq_map]; exact h
    have key : ∀ x ∈ 𝔟 • (⊤ : Submodule D E), bb.repr x a ∈ 𝔟 := by
      intro x hx
      induction hx using Submodule.smul_induction_on' with
      | smul y hy n hn =>
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hy
      | add x _ y _ hx hy =>
        rw [map_add, Finsupp.add_apply]
        exact add_mem hx hy
    simpa using key _ h'
  · intro h
    rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply]
    refine Ideal.sum_mem _ fun a _ => ?_
    show z a • bb a ∈ _
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (h a))

section Abs

variable {b : Base} {L : b.Fun} {Λ₀ : Type} [CommRing Λ₀] (c : Λ₀ →+* b.R)

noncomputable def eE {T₁ T₂ : Thick L} (f : T₁ ⟶ T₂) {ι E : Type} [CommRing E] [Algebra T₁.B E]
    (bb : Module.Basis ι T₁.B E) (e₀ : E →+* T₂.B) (he₀ : Function.Bijective e₀)
    (hθ : ∀ z, e₀ (algebraMap T₁.B E z) = Thick.Hom.φ f z) :
    (ι →₀ (OM L c).obj T₁) ≃ₗ[Λ₀] (OM L c).obj T₂ :=
  { (bb.repr.symm.toAddEquiv.trans (AddEquiv.ofBijective e₀ he₀) : (ι →₀ T₁.B) ≃+ T₂.B) with
    map_smul' := fun a z => by
      let z' : ι →₀ T₁.B := z
      have h1 : (show ι →₀ T₁.B from a • z) = T₁.i (c a) • z' := Finsupp.ext fun _ => rfl
      show e₀ (bb.repr.symm (show ι →₀ T₁.B from a • z)) = T₂.i (c a) * e₀ (bb.repr.symm z')
      rw [h1, map_smul, Algebra.smul_def, map_mul, hθ, Thick.Hom.comm f] }

theorem eE_single {T₁ T₂ : Thick L} (f : T₁ ⟶ T₂) {ι E : Type} [CommRing E] [Algebra T₁.B E]
    (bb : Module.Basis ι T₁.B E) (e₀ : E →+* T₂.B) (he₀ : Function.Bijective e₀)
    (hθ : ∀ z, e₀ (algebraMap T₁.B E z) = Thick.Hom.φ f z) (a : ι) (m : T₁.B) :
    e₀ (bb.repr.symm (Finsupp.single a m)) = Thick.Hom.φ f m * e₀ (bb a) := by
  rw [Module.Basis.repr_symm_single, Algebra.smul_def, map_mul, hθ]

end Abs

section Abs2

variable {b : Base} {L : b.Fun} {Λ₀ : Type} [CommRing Λ₀] (c : Λ₀ →+* b.R)

theorem ni_of_basis {ρ : ℕ → ℕ} (hρ : Slow ρ) (μ : Λ₀) (hμ : c μ ∈ b.I) {d : ℕ}
    {ι₁ ι₂ : SingleObj (Gam d) ⥤ Thick L} (θ : ι₁ ⟶ ι₂) {ι E : Type} [CommRing E]
    [Algebra (ι₁.obj (SingleObj.star _)).B E]
    (bb : Module.Basis ι (ι₁.obj (SingleObj.star _)).B E) (a₀ : ι) (hb₀ : bb a₀ = 1)
    (e₀ : E →+* (ι₂.obj (SingleObj.star _)).B) (he₀ : Function.Bijective e₀)
    (hθ : ∀ z, e₀ (algebraMap _ E z) = Thick.Hom.φ (θ.app (SingleObj.star _)) z)
    (χ : Gam d → ι → Λ₀) (hχ : ∀ g, χ g a₀ = 1)
    (heig : ∀ (g : Gam d) a, Thick.Hom.φ (ι₂.map (X := SingleObj.star _) (Y := SingleObj.star _) g) (e₀ (bb a)) =
      (ι₂.obj (SingleObj.star _)).i (c (χ g a)) * e₀ (bb a))
    (𝔞 : ℕ → Ideal b.R)
    (h𝔞₁ : ∀ r, (ι₁.obj (SingleObj.star _)).pdPow r = (𝔞 r).map (ι₁.obj (SingleObj.star _)).i)
    (h𝔞₂ : ∀ r, (ι₂.obj (SingleObj.star _)).pdPow r = (𝔞 r).map (ι₂.obj (SingleObj.star _)).i)
    (hflat : (ι₁.obj (SingleObj.star _)).i.Flat)
    (hmove : ∀ (k : Fin d) z, Thick.Hom.φ (ι₁.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k)) z - z ∈
      Ideal.span {(ι₁.obj (SingleObj.star _)).i (c μ)})
    (htw : ∀ a, a ≠ a₀ → ∃ (k : Fin d) (w ξ : b.R), c μ = (c (χ (gen k) a) - 1) * w * ξ ∧ IsNilpotent ξ ∧
      ∀ r, Ideal.span {ξ} * 𝔞 (ρ r) ≤ 𝔞 (ρ (r + 1))) :
    Nonempty (NI (Polynomial.X : Polynomial ℤ) (Functor.whiskerRight θ (pdFlt L c ρ hρ μ hμ).rees)) := by
  have hi : ∀ x, Thick.Hom.φ (θ.app (SingleObj.star _)) ((ι₁.obj (SingleObj.star _)).i x) = (ι₂.obj (SingleObj.star _)).i x :=
    Thick.Hom.comm _
  refine GlobalTheory.CompanionTheory.ReesBasis.main (pdFlt L c ρ hρ μ hμ) ι₁ ι₂ θ a₀ (eE c (θ.app _) bb e₀ he₀ hθ) χ ?_ ?_ hχ ?_ ?_
  · intro m
    refine (eE_single (θ.app _) bb e₀ he₀ hθ a₀ m).trans ?_
    rw [hb₀, map_one, mul_one]
    rfl
  · intro g a m
    have hn : ∀ x, Thick.Hom.φ (θ.app (SingleObj.star _)) (Thick.Hom.φ (ι₁.map (X := SingleObj.star _) (Y := SingleObj.star _) g) x) =
        Thick.Hom.φ (ι₂.map (X := SingleObj.star _) (Y := SingleObj.star _) g) (Thick.Hom.φ (θ.app (SingleObj.star _)) x) := fun x =>
      RingHom.congr_fun (congrArg Thick.Hom.φ (θ.naturality (X := SingleObj.star _) (Y := SingleObj.star _) g)) x
    refine (congrArg _ (eE_single (θ.app _) bb e₀ he₀ hθ a m)).trans (Eq.trans ?_ (eE_single (θ.app _) bb e₀ he₀ hθ a _).symm)
    show Thick.Hom.φ (ι₂.map (X := SingleObj.star _) (Y := SingleObj.star _) g) (Thick.Hom.φ (θ.app (SingleObj.star _)) m * e₀ (bb a)) =
      Thick.Hom.φ (θ.app (SingleObj.star _)) ((ι₁.obj (SingleObj.star _)).i (c (χ g a)) * Thick.Hom.φ (ι₁.map (X := SingleObj.star _) (Y := SingleObj.star _) g) m) * e₀ (bb a)
    rw [map_mul, map_mul, heig, hn, hi]
    ring
  · intro r z
    let z' : ι →₀ (ι₁.obj (SingleObj.star _)).B := z
    have hc : ((e₀.comp (algebraMap _ E)).comp (ι₁.obj (SingleObj.star _)).i) = (ι₂.obj (SingleObj.star _)).i :=
      RingHom.ext fun x => by rw [RingHom.comp_apply, RingHom.comp_apply, hθ, hi]
    have hm : (𝔞 (ρ r)).map (ι₂.obj (SingleObj.star _)).i =
        (((𝔞 (ρ r)).map (ι₁.obj (SingleObj.star _)).i).map (algebraMap _ E)).map e₀ := by
      rw [Ideal.map_map, Ideal.map_map, ← hc, RingHom.comp_assoc]
    have hq := Ideal.comap_map_of_bijective e₀ he₀ (I := ((𝔞 (ρ r)).map (ι₁.obj (SingleObj.star _)).i).map (algebraMap _ E))
    show e₀ (bb.repr.symm z') ∈ (ι₂.obj (SingleObj.star _)).pdPow (ρ r) ↔ ∀ a, z' a ∈ (ι₁.obj (SingleObj.star _)).pdPow (ρ r)
    rw [h𝔞₂, hm, h𝔞₁, ← mem_map_basis bb _ z', ← Ideal.mem_comap, hq]
  · intro a ha
    obtain ⟨k, w, ξ, hμ', hξ, hr⟩ := htw a ha
    obtain ⟨h1, h2⟩ := twist (ι₁.obj (SingleObj.star _)).i hflat
      (Thick.Hom.φ (ι₁.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k)))
      (RingHom.ext (Thick.Hom.comm _)) (c (χ (gen k) a)) w ξ (c μ) hμ' hξ (hmove k)
    refine ⟨k, h1, fun r x hx => ?_⟩
    have hx' : (show (ι₁.obj (SingleObj.star _)).B from x) ∈ (𝔞 (ρ r)).map (ι₁.obj (SingleObj.star _)).i := by
      rw [← h𝔞₁]; exact hx
    obtain ⟨y, hy, e⟩ := h2 _ _ hx'
    refine ⟨y, ?_, e⟩
    show y ∈ (ι₁.obj (SingleObj.star _)).pdPow (ρ (r + 1))
    rw [h𝔞₁]
    exact Ideal.map_mono (hr r) hy

end Abs2

section Lift

variable {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1)
  {κ : O →+* b.R ⧸ b.I} (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ)
  (δ : DividedPowers (b.I.map 𝓛.i)) (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0)
  (hn : IsNilpotent (b.p : b.R))

theorem hom_sub_mem (f : liftObj s ht 𝓛 δ hδ hp hn ⟶ liftObj s ht 𝓛 δ hδ hp hn) (z : 𝓛.D) :
    (show 𝓛.D from Thick.Hom.φ f z) - z ∈ b.I.map 𝓛.i := by
  obtain ⟨g, hc, -, -⟩ := GlobalTheory.CompanionTheory.ThickHom.main s ht 𝓛 δ hδ hp hn (liftObj s ht 𝓛 δ hδ hp hn)
  obtain ⟨f₀, -, hu⟩ := 𝓛.univ (𝓛.D ⧸ b.I.map 𝓛.i) ((Ideal.Quotient.mk _).comp 𝓛.i) 𝓛.j
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hx))
    (fun o x hx => 𝓛.hj o x hx)
  have e1 := hu (Ideal.Quotient.mk _) ⟨rfl, fun r z h => h⟩
  have e2 := hu ((Ideal.Quotient.mk (b.I.map 𝓛.i)).comp (Thick.Hom.φ f))
    ⟨RingHom.ext fun x => congrArg (Ideal.Quotient.mk (b.I.map 𝓛.i)) (Thick.Hom.comm f x), fun r z h => by
      have h1 : Ideal.Quotient.mk (b.I.map 𝓛.i) (Thick.Hom.φ f z) = g r := hc f r z h
      have h2 : Ideal.Quotient.mk (b.I.map 𝓛.i) z = g r := hc (𝟙 _) r z h
      exact h1.trans (h2.symm.trans h)⟩
  exact Ideal.Quotient.eq.1 (RingHom.congr_fun (e2.trans e1.symm) z)

end Lift

section Tower

variable {l : ℕ} [Fact l.Prime]

theorem root_eig (A : PAlg l) (f : A ⟶ A) (u c : ℕ → A.A) (hu : ∀ m, u (m + 1) ^ l = u m)
    (hc : ∀ m, c (m + 1) ^ l = c m) (h0 : PAlg.Hom.f f (c 0) = u 0 * c 0) (m : ℕ) :
    PAlg.Hom.f f (c m) = u m * c m := by
  have hinj : Function.Injective (fun x : A.A => x ^ l) := A.perf.bijective_frobenius.1
  induction m with
  | zero => exact h0
  | succ m ih =>
    apply hinj
    show PAlg.Hom.f f (c (m + 1)) ^ l = (u (m + 1) * c (m + 1)) ^ l
    rw [← map_pow, hc, ih, mul_pow, hu, hc]

theorem eig_prod (A : PAlg l) (ε : Eps l) (n : ℕ) (f : A ⟶ A) {d : ℕ} (c : Fin d → ℕ → A.A)
    (hc : ∀ k m, c k (m + 1) ^ l = c k m) (g : Fin d → ℕ)
    (h0 : ∀ j, PAlg.Hom.f f (c j 0) = A.s (ε.e 0) ^ (g j) * c j 0) (m : ℕ) (cc : Fin d → ℕ) :
    mapAcr f n (∏ k, A.toAcr n (WittVector.teichmuller l (c k m)) ^ cc k) =
      A.cris n (∏ k, ε.qk m ^ (g k * cc k)) * ∏ k, A.toAcr n (WittVector.teichmuller l (c k m)) ^ cc k := by
  rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hr := root_eig A f (fun m => A.s (ε.e m) ^ g k) (c k) (fun m => by
      show (A.s (ε.e (m + 1)) ^ g k) ^ l = A.s (ε.e m) ^ g k
      rw [pow_right_comm, ← map_pow, ← Units.val_pow_eq_pow_val, ε.succ]) (hc k) (h0 k) m
  rw [map_pow, map_pow, mapAcr_toAcr, mapW, WittVector.map_teichmuller, hr, map_mul, map_mul, map_pow, map_pow,
    Eps.cris_qk, pow_mul, ← mul_pow]

theorem tw_facts (ε : Eps l) (k : Bool) (n : ℕ) (hn : IsNilpotent (l : (base l).Acr n)) (ρ : ℕ → ℕ) (hρ : Slow ρ)
    (m c : ℕ) (hc : ¬ l ^ m ∣ c) :
    ∃ w ξ : (base l).Acr n, (base l).cris n ε.μ = ((base l).cris n (ε.qk m ^ c) - 1) * w * ξ ∧ IsNilpotent ξ ∧
      ∀ r, Ideal.span {ξ} * fil (DD k (base l) n) (ρ r) ≤ fil (DD k (base l) n) (ρ (r + 1)) := by
  obtain ⟨-, hq, hξ, hμ, -⟩ := GlobalTheory.T.epsilon_cyclotomic_element_properties ε
  have hl : (l : ℕ) ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hI : ∀ x ∈ JJ k (base l) n, IsNilpotent x := fun x hx =>
    GlobalTheory.CompanionTheory.ThickHom.isNilpotent_of_mem (DD k (base l) n) hl hn hx
  have h0 : IsNilpotent ((base l).cris n (ε.qk 0) - 1) := by
    have := hI _ (ε.μ_mem k (base l) n)
    rwa [Eps.μ, map_sub, map_one] at this
  obtain ⟨w, hw⟩ := GlobalTheory.CompanionTheory.RootsDivide.sub_one_dvd l Fact.out (fun j => (base l).cris n (ε.qk j)) hn
    (fun j => by rw [← map_pow, hq]) h0 m c hc
  set ξ := (base l).cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) with hξd
  have hξI : ξ ∈ JJ k (base l) n := fil_le k (base l) n (hξ (base l) n)
  refine ⟨w, ξ, ?_, hI _ hξI, fun r => ?_⟩
  · have : (base l).cris n ε.μ = ((base l).cris n (ε.qk 1) - 1) * ξ := by
      rw [hμ, map_mul, map_sub, map_one]
    rw [this, map_pow]
    have hw' : (base l).cris n (ε.qk 1) - 1 = ((base l).cris n (ε.qk m) ^ c - 1) * w := hw
    rw [hw']
  · rw [Ideal.span_singleton_mul_le_iff]
    intro x hx
    have h1 : ξ ∈ fil (DD k (base l) n) 1 := by
      have := GlobalTheory.CompanionTheory.PDMap.dpow_mem_fil (DD k (base l) n) hξI 1
      rwa [(DD k (base l) n).dpow_one hξI] at this
    have h2 := GlobalTheory.CompanionTheory.PDMap.fil_mul_le (DD k (base l) n) 1 (ρ r) (Ideal.mul_mem_mul h1 hx)
    exact GlobalTheory.CompanionTheory.PDMap.fil_anti (DD k (base l) n) (by have := hρ.2 r; omega) h2

end Tower

theorem main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (k : Bool) (n : ℕ) (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n)) (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0) (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (ε : Eps l) (ρ : ℕ → ℕ) (hρ : Slow ρ) (γ : Gam d →* End (liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn)) (γ' : Gam d →* End 𝒯.obj) (θ : SingleObj.functor γ ⟶ SingleObj.functor γ' ⋙ gE F κ k n), n ≠ 0 → (∀ j, (θ.app (SingleObj.star _)).φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) → (∀ a j, Thick.Hom.φ (γ a : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn) (𝓛.t j) = 𝓛.i (ε.qU n) ^ (Multiplicative.toAdd a j) * 𝓛.t j) → (∀ a j, PAlg.Hom.f (A := 𝒯.A) (B := 𝒯.A) (γ' a : 𝒯.obj ⟶ 𝒯.obj).1 (𝒯.c j 0).val = 𝒯.A.s (ε.e 0) ^ (Multiplicative.toAdd a j) * (𝒯.c j 0).val) → Nonempty (NI (Polynomial.X : Polynomial ℤ) (Functor.whiskerRight θ (flt F κ ε k n ρ hρ).rees)) := by
  intro l _ O _ F κ d s 𝒯 k n 𝓛 δ hδ hp hn ε ρ hρ γ γ' θ hn0 h1 h2 h3
  classical
  obtain ⟨X⟩ := GlobalTheory.CompanionTheory.RootAdjoin.nonempty_rootExt l Fact.out 𝓛.D 𝓛.t
  obtain ⟨e₀, hbij, hal, hr⟩ := GlobalTheory.T.root_extension_lift 𝒯 k n 𝓛 δ hδ hp hn X (θ.app (SingleObj.star _)) hn0 h1
  obtain ⟨-, -, -, -, hfil, -, -⟩ := GlobalTheory.T.period_ring_base_change_from_universal 𝒯.A n
  choose mm cc hb hnd using X.mono
  let χ : Gam d → X.ι → Acris l := fun g a =>
    if h : a = X.a₀ then 1 else ∏ j, ε.qk (mm a h) ^ (Multiplicative.toAdd g j * cc a h j)
  have hχ : ∀ g a (h : a ≠ X.a₀), χ g a = ∏ j, ε.qk (mm a h) ^ (Multiplicative.toAdd g j * cc a h j) :=
    fun g a h => dif_neg h
  have hflat := (GlobalTheory.CompanionTheory.LiftFlat.lift_flat 𝓛.i 𝓛.t 𝓛.et).1
  letI alg : Algebra ((SingleObj.functor γ).obj (SingleObj.star _)).B X.E := X.alg
  have hA := @ni_of_basis (bs l k n) (Lc F κ k n) (Acris l) _ ((base l).cris n) ρ hρ ε.μ (ε.μ_mem k (base l) n) d _ _ θ X.ι X.E _ alg X.b X.a₀ X.b_a₀ e₀ hbij hal χ (fun g => dif_pos rfl)
  refine hA ?_ (fun r => fil (DD k (base l) n) r) ?_ ?_ hflat ?_ ?_
  · intro g a
    show (mapAcr (γ' g : 𝒯.obj ⟶ 𝒯.obj).1 n) (e₀ (X.b a)) =
      (mapAcr 𝒯.A.fromBase n) ((base l).cris n (χ g a)) * e₀ (X.b a)
    by_cases ha : a = X.a₀
    · have h0 : χ g a = 1 := dif_pos ha
      have hb1 : e₀ (X.b a) = 1 := by rw [ha, X.b_a₀, map_one]
      rw [hb1, h0, map_one, map_one, map_one, mul_one]
    · have hbe : e₀ (X.b a) = ∏ j, 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j (mm a ha) : 𝒯.A.A)) ^ cc a ha j := by
        rw [hb a ha, map_prod]
        exact Finset.prod_congr rfl fun j _ => by rw [map_pow, hr]
      have hc : ∀ j m, (𝒯.c j (m + 1) : 𝒯.A.A) ^ l = 𝒯.c j m := fun j m => by
        rw [← Units.val_pow_eq_pow_val, 𝒯.c_succ]
      have he := eig_prod 𝒯.A ε n (γ' g : 𝒯.obj ⟶ 𝒯.obj).1 (fun j m => (𝒯.c j m : 𝒯.A.A)) hc
        (Multiplicative.toAdd g) (fun j => h3 g j) (mm a ha) (cc a ha)
      rw [hbe]
      refine he.trans ?_
      rw [← hχ g a ha]
      refine congrArg (· * _) ?_
      exact (mapAcr_cris 𝒯.A.fromBase n _).symm
  · intro r
    exact (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers (bs l k n).γ 𝓛.i δ hδ).1 r
  · intro r
    exact hfil k r
  · intro k' z
    have hq : 𝓛.i (ε.qU n) - 1 = 𝓛.i ((base l).cris n ε.μ) := by
      rw [Eps.μ, map_sub, map_sub, map_one, map_one, ← Eps.qU_val]
    let φ : 𝓛.D →+* 𝓛.D :=
      Thick.Hom.φ (γ (gen k') : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn)
    refine (GlobalTheory.CompanionTheory.LiftFlat.lift_flat 𝓛.i 𝓛.t 𝓛.et).2 ((bs l k n).I.map 𝓛.i) (𝓛.i ((base l).cris n ε.μ)) φ
      ?_ (RingHom.ext (Thick.Hom.comm _)) ?_ ?_ z
    · intro x hx
      refine GlobalTheory.CompanionTheory.ThickHom.isNilpotent_of_mem δ hp ?_ hx
      simpa using hn.map 𝓛.i
    · intro j
      have he : φ (𝓛.t j) = 𝓛.i (ε.qU n) ^ (Multiplicative.toAdd (gen k') j) * 𝓛.t j := h2 (gen k') j
      rw [he]
      have hd : 𝓛.i (ε.qU n) - 1 ∣ 𝓛.i (ε.qU n) ^ (Multiplicative.toAdd (gen k') j) - 1 := by
        simpa using sub_dvd_pow_sub_pow (𝓛.i (ε.qU n)) 1 (Multiplicative.toAdd (gen k') j)
      rw [hq] at hd
      refine Ideal.mem_span_singleton.2 ?_
      have : 𝓛.i (ε.qU n) ^ (Multiplicative.toAdd (gen k') j) * 𝓛.t j - 𝓛.t j =
          (𝓛.i (ε.qU n) ^ (Multiplicative.toAdd (gen k') j) - 1) * 𝓛.t j := by ring
      rw [this]
      exact hd.mul_right _
    · exact fun z => hom_sub_mem s rfl 𝓛 δ hδ hp hn (γ (gen k')) z
  · intro a ha
    obtain ⟨k', hk'⟩ := hnd a ha
    obtain ⟨w, ξ, h1', h2', h3'⟩ := tw_facts ε k n hn ρ hρ (mm a ha) (cc a ha k') hk'
    have hg : χ (gen k') a = ε.qk (mm a ha) ^ cc a ha k' := by
      rw [hχ _ _ ha, Finset.prod_eq_single k']
      · simp [gen]
      · intro j _ hj
        simp [gen, Pi.single_eq_of_ne hj]
      · simp
    exact ⟨k', w, ξ, by rw [hg]; exact h1', h2', h3'⟩

end GlobalTheory.CompanionTheory.TowerNI
