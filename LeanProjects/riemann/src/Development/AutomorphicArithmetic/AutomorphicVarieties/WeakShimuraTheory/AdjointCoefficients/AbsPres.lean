import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ObWeak
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ContConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Descend
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.TanInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ConeTan
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.SpDims
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.AdFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ObsPres
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem ap_lc {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {f : Γ → R}
    (h : AdicCont (⊥ : Ideal R) f) : IsLocallyConstant f := by
  refine IsLocallyConstant.desc f (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (h 1) fun x y hxy => ?_
  have := Ideal.Quotient.eq.1 hxy
  rwa [pow_one, Ideal.mem_bot, sub_eq_zero] at this

private theorem ap_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x * g x := fun N => by
  simp only [map_mul]
  exact (hf N).mul (hg N)

private theorem ap_haus (R : Type) [CommRing R] : IsHausdorff (⊥ : Ideal R) R :=
  ⟨fun x hx => by simpa [SModEq.bot] using hx 1⟩

theorem UpperTheory.V.Ws.X1.absPres :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → (∀ v, Φ.Mu v = ∅) → (∀ g ∈ Φ.N, a (Φ.ν g) = 1) → ∀ {Γb : Type} [Group Γb] [TopologicalSpace Γb] [IsTopologicalGroup Γb] [T2Space Γb] (π : Γ →* Γb), Φ.Quo π → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R), Φ.IsDef a c P → ∀ (rb : Γb →* M4 (ResidueField Λ)) (hb : ∀ g, ∃ x, IsGSp x (rb g)), rb.comp π = c.r → Module.Finite (ResidueField Λ) (Fr.coneH2 (Φ.loc π) (adSp rb hb) fun v => bor (c.n v)) → ∃ m : ℕ, HasPres Λ R m (Module.finrank (ResidueField Λ) (Fr.coneH2 (Φ.loc π) (adSp rb hb) fun v => bor (c.n v))) ∧ Module.finrank (ResidueField Λ) (Fr.H1C (Φ.loc π) (adSp rb hb) fun v => bor (c.n v)) + 2 ≤ m + Module.finrank (ResidueField Λ) (Fr.coneH0 (adSp rb hb) fun v => bor (c.n v)) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hS hMu hν Γb _ _ _ _ π hQ c hc R _ _ _ P hP rb hb hrb hfin
  have h2k : (2 : ResidueField Λ) ≠ 0 := hS.ok.two.ne_zero
  have h2 : IsUnit (2 : Λ) := by
    by_contra h
    exact h2k (by rw [← map_ofNat (residue Λ) 2]; exact (residue_eq_zero_iff _).2 h)

  obtain ⟨r, hr, hrc⟩ := (X1.descend Φ π hQ (maximalIdeal R)).1 P.r hP.1.pair.kill hP.1.cont
  have hνc : AdicCont (maximalIdeal Λ) fun g => (((Units.map a.toMonoidHom).comp Φ.ν g : Λˣ) : Λ) := by
    have := ap_mul (hS.cont 0) (hS.cont (Fin.rev 0))
    refine (congrArg _ (funext fun g => ?_)).mp this
    rw [← map_mul, ← Units.val_mul, hS.ok.mul]
    rfl
  obtain ⟨ν, hνe, hνc'⟩ := (X1.descend Φ π hQ (maximalIdeal Λ)).2 ((Units.map a.toMonoidHom).comp Φ.ν)
    (fun g hg => Units.ext (hν g hg)) hνc
  have hν' : ∀ g, (ν (π g) : Λ) = a (Φ.ν g) := fun g => congrArg Units.val (DFunLike.congr_fun hνe g)
  have hr' : ∀ g, r (π g) = P.r g := fun g => DFunLike.congr_fun hr g
  have hrb' : ∀ g, rb (π g) = c.r g := fun g => DFunLike.congr_fun hrb g
  haveI := ap_haus (ResidueField Λ)
  obtain ⟨rb', hrb2, hrbc⟩ := (X1.descend Φ π hQ (⊥ : Ideal (ResidueField Λ))).1 c.r hc.pair.kill hc.cont
  have hrr : rb' = rb := MonoidHom.ext fun g => by
    obtain ⟨g, rfl⟩ := hQ.onto g
    rw [hrb']
    exact DFunLike.congr_fun hrb2 g
  subst hrr
  have hWP : WP (Φ.loc π) (fun g => algebraMap Λ R (ν g)) r P.n := by
    refine ⟨fun g => ?_, fun v => (hP.1.pair.low v).1, fun v s => ?_⟩
    · obtain ⟨g, rfl⟩ := hQ.onto g
      rw [hν', hr']
      exact hP.1.pair.mult g
    · show IsUp (adj (P.n v) * r (π s) * P.n v)
      rw [hr']
      exact hP.1.pair.flag v s s.2
  have hob := X1.obWeak h2 (Φ.loc π) (fun v => hQ.cont.comp continuous_subtype_val) ν r P.n hνc' hWP hrc
    rb' c.n hb (fun g => by
      obtain ⟨g, rfl⟩ := hQ.onto g
      rw [hr', hrb', ← hP.1.red]
      rfl) (fun v => by rw [← hP.1.red]; rfl)
  obtain ⟨m, π₀, f, hπ₀, hker, hcard⟩ := obs_pres Λ R
    (Fr.coneH2 (Φ.loc π) (adSp rb' hb) fun v => bor (c.n v)) (fun A _ _ _ p hp hm κ _ ε hε hind => by
      obtain ⟨o, ho⟩ := hob A p hp hm κ ε hε hind
      refine ⟨o, fun d hd A' _ _ _ p' p'' η k1 k2 k3 k4 k5 => ?_⟩
      obtain ⟨q1, q2, q3⟩ := ho d hd A' p' p'' η k1 k2 k3 k4 k5
      exact X1.sect Φ l a hS hMu π hQ c hc R P hP ν r hν' hr A' p'' q1 q2 q3)
  refine ⟨m, ⟨π₀, f, hπ₀, hker⟩, ?_⟩
  obtain ⟨t, ht⟩ := X1.tanInj Φ l a hS hMu π hQ c hc R P hP rb' hb hrb
  have hq : 1 < Nat.card (ResidueField Λ) := Finite.one_lt_card
  haveI : Finite (R →ₐ[Λ] DualNumber (ResidueField Λ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  haveI hT := Finite.of_injective t ht
  have hle := Nat.card_le_card_of_injective t ht
  have hMF : Module.Finite (ResidueField Λ) (TanC (Φ.loc π) (adSp rb' hb) (fun v => bor (c.n v))
    (fun v => nil (c.n v)) (π Φ.g0) (tor (ResidueField Λ))) := Module.Finite.of_finite
  rw [hcard, Module.natCard_eq_pow_finrank (K := ResidueField Λ), Nat.pow_le_pow_iff_right hq] at hle
  obtain ⟨d1, d2⟩ := X1.spDims (ResidueField Λ) h2k
  obtain ⟨a1, a2⟩ := X1.adFacts rb' hb
  have hct := X1.coneTan (Φ.loc π) (adSp rb' hb) (fun v => bor (c.n v)) (fun v => nil (c.n v)) (π Φ.g0)
    (tor (ResidueField Λ)) (a1 fun i j => ap_lc (hrbc i j)).2
    (fun v s => a2 (c.n v) _ (hc.pair.low v).1
      (by
        show IsUp (adj (c.n v) * rb' (π s) * c.n v)
        rw [hrb']
        exact hc.pair.flag v s s.2)
      (by
        show IsUp (adj (c.n v) * rb' (π s)⁻¹ * c.n v)
        rw [← map_inv, hrb']
        exact hc.pair.flag v _ (inv_mem s.2)))
    (fun v => (d2 _ (hc.pair.low v).1).2) hMF
  rw [d1] at hct
  omega
