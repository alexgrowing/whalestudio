import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueLatOfChartBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordField
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralSectionLatticeMultipleStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.OriginEps

open AlgebraicGeometry CategoryTheory

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem mem_adjoin_rat_of_regular {κ : Type} {x : κ → Ω} (hT : CoordTie ℤ ξ x)
    {c : κ} (hc : x c ≠ 0) {f : Ω}
    (hf : ∀ p : Cpt ξ, InChart ξ x c p → (∀ r : ℕ, r.Prime → ¬ InFibre ξ r p) → f ∈ regAt ξ p) :
    f ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x c) := by
  classical
  set B := Algebra.adjoin ℚ (Set.range fun j => x j / x c) with hB
  have hle : ∀ a ∈ chartRing ℤ x c, a ∈ B := by
    intro a ha
    have h2 : chartRing ℤ x c ≤ B.restrictScalars ℤ := Algebra.adjoin_le Algebra.subset_adjoin
    exact h2 ha
  let I : Ideal (chartRing ℤ x c) :=
    { carrier := {a | (a : Ω) * f ∈ B}
      add_mem' := fun {u v} hu hv => by
        show ((u + v : chartRing ℤ x c) : Ω) * f ∈ B
        rw [Subalgebra.coe_add, add_mul]
        exact add_mem hu hv
      zero_mem' := by
        show ((0 : chartRing ℤ x c) : Ω) * f ∈ B
        simp
      smul_mem' := fun a u hu => by
        show ((a • u : chartRing ℤ x c) : Ω) * f ∈ B
        rw [smul_eq_mul, Subalgebra.coe_mul, _root_.mul_assoc]
        exact mul_mem (hle _ a.2) hu }
  let T : Submonoid (chartRing ℤ x c) :=
    { carrier := {u | ∃ b : ℕ, b ≠ 0 ∧ (u : Ω) = b}
      one_mem' := ⟨1, one_ne_zero, by simp⟩
      mul_mem' := by
        rintro u v ⟨b, hb, hu⟩ ⟨b', hb', hv⟩
        exact ⟨b * b', mul_ne_zero hb hb', by rw [Subalgebra.coe_mul, hu, hv]; push_cast; rfl⟩ }
  by_contra hcon
  have hdisj : Disjoint (I : Set (chartRing ℤ x c)) (T : Set (chartRing ℤ x c)) := by
    rw [Set.disjoint_left]
    rintro u hu ⟨b, hb, hub⟩
    have hu' : (b : Ω) * f ∈ B := by rw [← hub]; exact hu
    apply hcon
    have h2 := B.smul_mem hu' ((b : ℚ)⁻¹)
    have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 hb
    have e : ((b : ℚ)⁻¹) • ((b : Ω) * f) = f := by
      rw [Algebra.smul_def, map_inv₀, map_natCast, ← _root_.mul_assoc, inv_mul_cancel₀ hb0, _root_.one_mul]
    rwa [e] at h2
  obtain ⟨P, hP, hIP, hPT⟩ := Ideal.exists_le_prime_disjoint I T hdisj
  obtain ⟨p, hp, hpP⟩ := TieVB.exists_point hT hc P hP
  have h0 : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r p := by
    intro r hr hfib
    have hrT : (r : chartRing ℤ x c) ∈ T := ⟨r, hr.ne_zero, by simp⟩
    have hnot : (r : chartRing ℤ x c) ∉ P := fun h => Set.disjoint_left.1 hPT h hrT
    have hu := not_not.1 (mt (hpP (r : chartRing ℤ x c)).2 hnot)
    apply hfib
    simpa using hu
  obtain ⟨s, hsA, hsu, hsf⟩ := TieVB.exists_den hT hp (hf p hp h0)
  have hI : (⟨s, hsA⟩ : chartRing ℤ x c) ∈ I := hle _ hsf
  exact (hpP ⟨s, hsA⟩).1 (hIP hI) hsu

theorem adjoin_segre_le {K : Type} [Fintype K] {ι : K → Type} {y : (Σ k, ι k) → Ω} (c : (k : K) → ι k) :
    Algebra.adjoin ℚ (Set.range fun c' : (k : K) → ι k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) ≤
      Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨c', rfl⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ ∈ _
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨k, c' k⟩, rfl⟩

theorem zpow_sum_of_ne {R : Type} {a : Ω} (ha : a ≠ 0) (s : Finset R) (f : R → ℤ) :
    a ^ (∑ r ∈ s, f r) = ∏ r ∈ s, a ^ f r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert r s hr ih => rw [Finset.sum_insert hr, Finset.prod_insert hr, zpow_add₀ ha, ih]

theorem eps_identity {K R : Type} [Fintype K] [Fintype R] {Y : K → Ω} (hY : ∀ k, Y k ≠ 0) (xd : R → K → ℤ)
    {e : R → Ω} (n : R → ℤ) (A : K → ℤ) (k₀ : K) (hA₀ : A k₀ = 1)
    (hA : ∀ k, k ≠ k₀ → A k = 0) (q : ℕ) (s : Ω) :
    (s * ∏ r, e r ^ n r) * ∏ k, Y k ^ (-(∑ r, (-n r) * xd r k + (-(q : ℤ)) * A k)) =
      s * Y k₀ ^ q / ∏ r, ((∏ k, Y k ^ xd r k) * e r) ^ (-n r) := by
  have h1 : ∀ k, Y k ^ (-(∑ r, (-n r) * xd r k + (-(q : ℤ)) * A k)) =
      (∏ r, (Y k ^ xd r k) ^ n r) * Y k ^ ((q : ℤ) * A k) := by
    intro k
    have e1 : -(∑ r, (-n r) * xd r k + (-(q : ℤ)) * A k) = ∑ r, xd r k * n r + (q : ℤ) * A k := by
      rw [neg_add, ← Finset.sum_neg_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun r _ => by ring
      · ring
    rw [e1, zpow_add₀ (hY k), zpow_sum_of_ne (hY k)]
    simp only [zpow_mul]
  have h2 : ∏ k, Y k ^ ((q : ℤ) * A k) = Y k₀ ^ q := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by rw [hA k hk]; simp) (fun h => absurd (Finset.mem_univ _) h), hA₀]
    simp
  have h3 : ∏ r, ((∏ k, Y k ^ xd r k) * e r) ^ (-n r) =
      ((∏ k, ∏ r, (Y k ^ xd r k) ^ n r) * ∏ r, e r ^ n r)⁻¹ := by
    simp only [zpow_neg, Finset.prod_inv_distrib]
    congr 1
    simp only [mul_zpow, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun r _ => (Finset.prod_zpow _ _ _).symm
  simp only [h1, Finset.prod_mul_distrib]
  rw [h2, h3, div_inv_eq_mul]
  ring

end General

theorem section_on_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (nu : Wt (CMType H) (D.p + D.q)), (∀ r, (Fx.n r : ℝ) = (Fx.kA * Fx.q' : ℕ) * nu r.1 r.2) → ∃ (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ j, (n₀ j : ℝ) = (Fx.kA * Fx.q' : ℕ) * RM.coef nu (-1) j) ∧ 0 < N₀ ∧ ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 ∧ ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ∈ chartLatNm RM.y (combLine (RM.line 1) n₀).a 1 := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx o nu hn
  classical
  haveI : CharZero c.F := inferInstance
  haveI : CharZero RM.Ω := charZero_of_injective_ringHom o.𝔐.cst.injective
  have hkA : (RM.kA : ℝ) = Fx.kA := by exact_mod_cast o.kA_eq
  have hkpos : (0 : ℝ) < Fx.kA := by rw [← hkA]; exact_mod_cast RM.kA_pos
  let n₀ : Option (RootIx D) → ℤ := fun j => j.elim (-(Fx.q' : ℤ)) fun r => -Fx.n r
  have hs0 : o.g Fx.sE * ∏ r, o.e r ^ Fx.n r ≠ 0 :=
    mul_ne_zero ((map_ne_zero o.g).2 Fx.sE_ne)
      (Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _ (o.lines r).1)
  have ha : ∀ k, (combLine (RM.line 1) n₀).a k =
      ∑ r, (-Fx.n r) * RM.xdeg r k + (-(Fx.q' : ℤ)) * RM.A.a k := by
    intro k
    show (∑ j, n₀ j • (RM.line 1 j).a) k = _
    rw [Finset.sum_apply, Fintype.sum_option, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun r _ => ?_
      simp [n₀, RootModel.line, RM.x_deg]
  have key : ∀ c' : ∀ k, RM.ι k, (∀ k, RM.y ⟨k, c' k⟩ ≠ 0) →
      IsIntegral (Algebra.adjoin ℚ (Set.range fun p : Σ k, RM.ι k => RM.y p / RM.y ⟨p.1, c' p.1⟩))
        ((o.g Fx.sE * ∏ r, o.e r ^ Fx.n r) * ∏ k, RM.y ⟨k, c' k⟩ ^ (-((combLine (RM.line 1) n₀).a k))) := by
    intro c' hc'
    have hx : (∏ k, RM.y ⟨k, c' k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc' k
    have ya : o.g (Fx.yf (o.ix.symm (c' o.k₀))) = RM.y ⟨o.k₀, c' o.k₀⟩ := by
      rw [← o.y_eq, Equiv.apply_symm_apply]
    have hfeq : (o.g Fx.sE * ∏ r, o.e r ^ Fx.n r) * ∏ k, RM.y ⟨k, c' k⟩ ^ (-((combLine (RM.line 1) n₀).a k)) =
        o.g Fx.sE * o.g (Fx.yf (o.ix.symm (c' o.k₀))) ^ Fx.q' /
          ∏ r, ((∏ k, RM.y ⟨k, c' k⟩ ^ RM.xdeg r k) * o.e r) ^ (-Fx.n r) := by
      simp only [ha]
      rw [ya]
      exact eps_identity hc' RM.xdeg Fx.n RM.A.a o.k₀ o.A_deg.1 o.A_deg.2 Fx.q' _
    have hreg : ∀ p : Cpt o.𝔐.ξ, InChart o.𝔐.ξ (fun c'' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c'' k⟩) c' p →
        (∀ r : ℕ, r.Prime → ¬ InFibre o.𝔐.ξ r p) →
        o.g Fx.sE * o.g (Fx.yf (o.ix.symm (c' o.k₀))) ^ Fx.q' /
          ∏ r, ((∏ k, RM.y ⟨k, c' k⟩ ^ RM.xdeg r k) * o.e r) ^ (-Fx.n r) ∈ regAt o.𝔐.ξ p := by
      intro p hp hp0
      have hch : InChart o.𝔐.ξ (fun i' => o.g (Fx.yf i')) (o.ix.symm (c' o.k₀)) p := by
        refine ⟨?_, fun j => ?_⟩
        · show o.g (Fx.yf (o.ix.symm (c' o.k₀))) ≠ 0
          rw [ya]; exact hc' _
        · show o.g (Fx.yf j) / o.g (Fx.yf (o.ix.symm (c' o.k₀))) ∈ _
          rw [ya, ← o.y_eq]
          exact Lat.block_ratio_mem hp o.k₀ (o.ix j)
      have ht := GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.tens_isGenAt (Λ := o.Fl.rootLat) (fun r => -Fx.n r) (p := p)
        (s := fun r => (∏ k, RM.y ⟨k, c' k⟩ ^ RM.xdeg r k) * o.e r) fun r =>
          ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc' k)) (o.lines r).1,
            (o.lines r).2 _ trivial c' hp⟩
      exact (o.eff p hp0 _ _ hch ht).1
    have hB := adjoin_segre_le c' (mem_adjoin_rat_of_regular o.𝔐.tie hx hreg)
    rw [hfeq]
    exact isIntegral_algebraMap (x := (⟨_, hB⟩ : Algebra.adjoin ℚ
      (Set.range fun p : Σ k, RM.ι k => RM.y p / RM.y ⟨p.1, c' p.1⟩)))
  obtain ⟨N₀, hN, hmem⟩ := GlobalTheory.T.integral_section_lattice_multiple RM.K RM.ι RM.Ω RM.y 0 (combLine (RM.line 1) n₀).a _ key
  refine ⟨n₀, N₀, ?_, hN, ?_, ?_⟩
  · intro j
    cases j with
    | none =>
      show ((-(Fx.q' : ℤ) : ℤ) : ℝ) = ((Fx.kA * Fx.q' : ℕ) : ℝ) * (-1 / (RM.kA : ℝ))
      rw [hkA]
      push_cast
      field_simp
    | some r =>
      show ((-Fx.n r : ℤ) : ℝ) = ((Fx.kA * Fx.q' : ℕ) : ℝ) * (-nu r.1 r.2)
      push_cast
      rw [hn r]
      push_cast
      ring
  · rw [_root_.mul_assoc]
    exact mul_ne_zero (Nat.cast_ne_zero.2 hN.ne') hs0
  · rw [_root_.mul_assoc]
    exact hmem

end GlobalTheory.CompanionTheory.Ar.Small.OriginEps
