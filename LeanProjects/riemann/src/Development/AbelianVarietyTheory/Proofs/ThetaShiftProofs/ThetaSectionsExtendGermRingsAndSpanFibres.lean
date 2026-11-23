import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsBasisFSum
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCoeffMemSubfield
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RepTransport
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjIsAbelianSchemeDimRigidifiedSym

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.FibreFrame

section Calc

variable {K R : Type} [CommRing K] [CommRing R] {X Z S : Scheme.{0}} {L : LB Z} {m : ℕ}

theorem fib_fst {G : Over S} {y : Sp R ⟶ S} (x : Over.mk y ⟶ G) : fib x ≫ pullback.fst _ _ = x.left :=
  pullback.lift_fst _ _ _

theorem fib_snd {G : Over S} {y : Sp R ⟶ S} (x : Over.mk y ⟶ G) :
    fib x ≫ pullback.snd _ _ = spMap (RingHom.id R) :=
  (pullback.lift_snd _ _ _).trans (Spec.map_id _).symm

theorem Rep.trans {π : X ⟶ Z} {p : X ⟶ Sp K} {n N : ℕ} {σ : Fin n → SecP L π m} {β : Fin N → SecP L π m}
    {s : SecP L π m} {r : Fin n → K} {c : Fin n → Fin N → K} (h : Rep p σ s r) (hc : ∀ i, Rep p β (σ i) (c i)) :
    Rep p β s fun l => ∑ i, r i * c i l := fun R _ f q j hq hj => by
  rw [h R f q j hq hj]
  simp only [map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc i R f q j hq hj, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => (_root_.mul_assoc _ _ _).symm

theorem rep_self {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (i : Fin n) :
    Rep p σ (σ i) (Pi.single i 1) := fun R _ f q j _ _ => by
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]
  simp

theorem Rep.hasVal {π : X ⟶ Z} {p : X ⟶ Sp K} {n : ℕ} {σ : Fin n → SecP L π m} {s : SecP L π m} {r : Fin n → K}
    (h : Rep p σ s r) {q : Sp K ⟶ X} (hq : q ≫ p = spMap (RingHom.id K)) {τ : L.ι → K} {a : Fin n → K}
    (ha : ∀ i, HasVal (σ i) q τ (a i)) : HasVal s q τ (∑ i, r i * a i) := fun j hj => by
  rw [h K _ q j hq hj, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [ha i j hj, RingHom.id_apply, _root_.mul_assoc]

theorem exists_chart {F : Type} [Field F] (hL : L.IsLB) (x : Sp F ⟶ Z) : ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ (x (default : PrimeSpectrum F))))
  refine ⟨j, fun p _ => ?_⟩
  obtain rfl : p = (default : PrimeSpectrum F) := Subsingleton.elim (α := PrimeSpectrum F) _ _
  exact hj

theorem le_preimage_of_field {F F' : Type} [Field F] [Field F'] (ρ : F →+* F') {x : Sp F ⟶ Z} {U : Z.Opens}
    (h : ⊤ ≤ (spMap ρ ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
  obtain rfl : p = spMap ρ (default : PrimeSpectrum F') := Subsingleton.elim (α := PrimeSpectrum F) _ _
  exact h (x := (default : PrimeSpectrum F')) trivial

theorem le_preimage_of_ev (Γ : Germs) (w : ℂ) {x : Sp (Γ.R w) ⟶ Z} {U : Z.Opens}
    (h : ⊤ ≤ (spMap (Γ.ev w).toRingHom ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  have : IsLocalRing (Γ.R w) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases ha : Γ.ev w a = 0
    · exact Or.inr (Γ.unit w _ (by simp [ha]))
    · exact Or.inl (Γ.unit w _ ha)
  have hl : IsLocalHom (CommRingCat.ofHom (Γ.ev w).toRingHom).hom := ⟨fun a ha => Γ.unit w a ha.ne_zero⟩
  refine (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of (Γ.R w)) x ?_).ge
  have := h (x := IsLocalRing.closedPoint ℂ) trivial
  rw [← Spec_closedPoint (f := CommRingCat.ofHom (Γ.ev w).toRingHom)]
  exact this

theorem mem_of_inverse {k F : Type} [Field k] [Field F] [Algebra k F] (M : IntermediateField k F) {n N : ℕ}
    {g : Fin N → Fin n → F} {c : Fin n → Fin N → F} (hg : ∀ i a, g i a ∈ M)
    (h₁ : ∀ a b, ∑ i, c a i * g i b = (Pi.single a 1 : Fin n → F) b)
    (h₂ : ∀ i l, ∑ a, g i a * c a l = (Pi.single i 1 : Fin N → F) l) (a : Fin n) (l : Fin N) : c a l ∈ M := by
  obtain ⟨pr, hpr⟩ := (Algebra.linearMap M F).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap M F).injective)
  have h0 : ∀ x : M, pr x = x := fun x => LinearMap.congr_fun hpr x
  have h₃ : ∀ b, ∑ i, (pr (c a i) : F) * g i b = (Pi.single a 1 : Fin n → F) b := fun b => by
    have e : ∀ i, c a i * g i b = (⟨_, hg i b⟩ : M) • c a i := fun i => mul_comm _ _
    have := congrArg (fun x => (pr x : F)) (h₁ a b)
    simp only [e, map_sum, map_smul, smul_eq_mul] at this
    have e' : (pr ((Pi.single a 1 : Fin n → F) b) : F) = (Pi.single a 1 : Fin n → F) b := by
      by_cases hb : b = a
      · subst hb
        rw [Pi.single_eq_same]
        exact congrArg Subtype.val (h0 1)
      · rw [Pi.single_eq_of_ne hb, map_zero]
        rfl
    rw [← e', ← this, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have : c a l = pr (c a l) := by
    calc c a l = ∑ b, (∑ i, (pr (c a i) : F) * g i b) * c b l := by simp [h₃, Pi.single_apply]
      _ = ∑ i, (pr (c a i) : F) * ∑ b, g i b * c b l := by
        simp only [Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
        exact Finset.sum_comm
      _ = pr (c a l) := by simp [h₂, Pi.single_apply]
  rw [this]
  exact (pr _).2

end Calc

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {S : Scheme.{0}}
  {A : AnArc (𝓞 E)} {t : SAB H S} {y : Sp ℂ⸨X⸩ ⟶ S} (Φ : GenPts A t y) {j : ℕ} [NeZero j]

omit [NeZero j] in
theorem hasVal_unique {s : SecP t.PP.L (pullback.fst t.G.hom y) j} {v : A.V} {a b : ℂ⸨X⸩}
    (ha : HasVal s (fib (Φ.x v)) (Φ.τ v) a) (hb : HasVal s (fib (Φ.x v)) (Φ.τ v) b) : a = b := by
  obtain ⟨k, hk⟩ := exists_chart t.PP.isLB (Φ.x v).left
  have hk' : ⊤ ≤ (fib (Φ.x v) ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U k := by rw [fib_fst]; exact hk
  exact (((Φ.frm v).1 k hk).pow j).mul_right_cancel ((ha k hk').symm.trans (hb k hk'))

theorem rep_of_hasVal {n : ℕ} {σ : Fin n → SecP t.PP.L (pullback.fst t.G.hom y) j}
    {s : SecP t.PP.L (pullback.fst t.G.hom y) j} {r : Fin n → ℂ⸨X⸩} {φ : Fin n → A.V → ℂ⸨X⸩}
    (hσ : ∀ i v, HasVal (σ i) (fib (Φ.x v)) (Φ.τ v) (φ i v))
    (hs : ∀ v, HasVal s (fib (Φ.x v)) (Φ.τ v) (∑ i, r i * φ i v)) : Rep (pullback.snd t.G.hom y) σ s r := by
  have h0 := Φ.sep j (comb (pullback.snd t.G.hom y) (Fin.cons (-1) r : Fin (n + 1) → _) (Fin.cons s σ)) fun v => by
    have := (rep_comb (pullback.snd t.G.hom y) (Fin.cons s σ : Fin (n + 1) → _) (Fin.cons (-1) r)).hasVal
      (fib_snd (Φ.x v)) (τ := Φ.τ v) (a := Fin.cons (∑ i, r i * φ i v) fun i => φ i v)
      (Fin.cases (hs v) fun i => hσ i v)
    simpa [Fin.sum_univ_succ] using this
  intro R _ f q k hq hk
  have h1 := rep_comb (pullback.snd t.G.hom y) (Fin.cons s σ : Fin (n + 1) → _) (Fin.cons (-1) r) R f q k hq hk
  have h2 := (congrArg (valR q _) (h0 fun _ => k)).trans
    ((HolHom.valR_eq q _ (le_wchart hk) 0).trans (map_zero _))
  have h3 := h1.symm.trans h2
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, map_neg, map_one] at h3
  linear_combination -h3

theorem exists_coeff (hA : AnFin A) {N : ℕ} {β : Fin N → SecP t.PP.L (pullback.fst t.G.hom y) j}
    (hβ : ∀ s, ∃! c, Rep (pullback.snd t.G.hom y) β s c)
    (hK : ∀ i v a, HasVal (β i) (fib (Φ.x v)) (Φ.τ v) a → a ∈ Conv.convLaurent) :
    ∃ (T : ℝ) (a : A.X → ((Fin A.gB → ℂ) → ℂ) → Fin N → Conv.halfRing T),
      (∀ α, ∀ th ∈ A.Theta j α, Rep (pullback.snd t.G.hom y) β (Φ.sig j α th) fun i => a α th i) ∧
      ∃ (n : ℕ) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ) (g : Fin N → Fin n → Conv.halfRing T),
        (∀ k, th k ∈ A.Theta j (α k)) ∧ ∀ i l, ∑ k, g i k * a (α k) (th k) l = (Pi.single i 1 : Fin N → _) l := by
  classical
  obtain ⟨n, α, th, -, hth, hli, -, hsp⟩ := GlobalTheory.AnArc.exists_basis_FSum _ A hA j
  choose a ha _ using fun α th => hβ (Φ.sig j α th)
  have hv := fun k => Φ.val j (α k) (th k) (hth k)
  have h1 : ∀ i, ∃ g : Fin n → ℂ⸨X⸩, (∀ k, g k ∈ Conv.convLaurent) ∧
      ∀ v, HasVal (β i) (fib (Φ.x v)) (Φ.τ v) (∑ k, g k * A.FSum j (α k) (th k) v) := fun i => by
    obtain ⟨f, hf, hfv⟩ := Φ.span j (β i)
    obtain ⟨T, ⟨n', r, α', th', h1, h2⟩, -⟩ := GlobalTheory.ArcPts.exists_isComb_halfRing _ A hA j f hf fun v => hK i v _ (hfv v)
    choose r' hr' e using fun k => hsp (α' k) (th' k) (h1 k).2
    refine ⟨fun k => ∑ k', r k' * r' k' k, fun k => Conv.halfRing_le_convLaurent T
      (sum_mem fun k' _ => mul_mem (h1 k').1 (hr' k' k T)), fun v => ?_⟩
    have e' : ∑ k, (∑ k', r k' * r' k' k) * A.FSum j (α k) (th k) v = f v := by
      rw [h2 v]
      simp only [e, Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
      exact Finset.sum_comm
    rw [e']
    exact hfv v
  choose g hg hgv using h1
  have h₂ : ∀ i l, ∑ k, g i k * a (α k) (th k) l = (Pi.single i 1 : Fin N → _) l := fun i =>
    congrFun ((hβ (β i)).unique ((rep_of_hasVal Φ hv (hgv i)).trans fun k => ha _ _) (rep_self _ _ i))
  have h₁ : ∀ k b, ∑ i, a (α k) (th k) i * g i b = (Pi.single k 1 : Fin n → _) b := fun k => by
    refine Fintype.linearIndependent_iffₛ.1 hli _ _ (funext fun v => ?_)
    have := hasVal_unique Φ ((ha (α k) (th k)).hasVal (fib_snd _) fun i => hgv i v) (hv k v)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, ite_mul, _root_.one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← this]
    simp only [Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
    exact Finset.sum_comm
  choose Tg hTg using fun i k => Conv.mem_convLaurent_iff_halfRing.1 (hg i k)
  choose Tc hTc using fun k l => Conv.mem_convLaurent_iff_halfRing.1 (mem_of_inverse _ hg h₁ h₂ k l)
  obtain ⟨T₁, hT₁⟩ := (Set.finite_range fun p : Fin N × Fin n => Tg p.1 p.2).bddAbove
  obtain ⟨T₂, hT₂⟩ := (Set.finite_range fun p : Fin N × Fin n => Tc p.2 p.1).bddAbove
  have hgT : ∀ i k, g i k ∈ Conv.halfRing (max T₁ T₂) := fun i k =>
    Conv.halfRing_mono ((hT₁ ⟨(i, k), rfl⟩).trans (le_max_left _ _)) (hTg i k)
  have haT : ∀ α', ∀ th' ∈ A.Theta j α', ∀ l, a α' th' l ∈ Conv.halfRing (max T₁ T₂) := fun α' th' h' l => by
    obtain ⟨r, hr, e⟩ := hsp α' th' h'
    rw [(hβ _).unique (ha α' th') ((rep_of_hasVal Φ hv fun v => e v ▸ Φ.val j α' th' h' v).trans fun k => ha _ _)]
    exact sum_mem fun k _ => mul_mem (hr k _)
      (Conv.halfRing_mono ((hT₂ ⟨(l, k), rfl⟩).trans (le_max_right _ _)) (hTc k l))
  refine ⟨max T₁ T₂, fun α' th' l => if h : th' ∈ A.Theta j α' then ⟨_, haT α' th' h l⟩ else 0,
    fun α' th' h => by simpa only [dif_pos h] using ha α' th', n, α, th, fun i k => ⟨_, hgT i k⟩, hth, fun i l => ?_⟩
  apply Subtype.ext
  simp only [dif_pos (hth _)]
  rw [AddSubmonoidClass.coe_finsetSum]
  refine (h₂ i l).trans ?_
  by_cases h : l = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

end Generic

theorem extend_of_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
    {S : Scheme.{0}} {A : AnArc (𝓞 E)} {t : SAB H S} {y : Sp ℂ⸨X⸩ ⟶ S} (Φ : GenPts A t y) (Γ : Germs)
    (Ψ : SpecPts Φ Γ) (hA : AnFin A) (hR : Φ.Rational) (j : ℕ) [NeZero j] {V : S.Opens} (hy : ⊤ ≤ y ⁻¹ᵁ V) {N : ℕ}
    (β : ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S), ⊤ ≤ y ⁻¹ᵁ V → Fin N → SecP t.PP.L (pullback.fst t.G.hom y) j)
    (hc : ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S) (hy : ⊤ ≤ y ⁻¹ᵁ V) (R' : Type) [CommRing R'] (y' : Sp R' ⟶ S)
      (hy' : ⊤ ≤ y' ⁻¹ᵁ V) (C : Type) [CommRing C] (q : Sp C ⟶ pullback t.G.hom y) (q' : Sp C ⟶ pullback t.G.hom y')
      (i : Fin N) (k : t.PP.L.ι), q ≫ pullback.fst _ _ = q' ≫ pullback.fst _ _ →
      ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U k → ArcPts.sval (β R y hy i) q k = ArcPts.sval (β R' y' hy' i) q' k)
    (hβ : ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S) (hy : ⊤ ≤ y ⁻¹ᵁ V) (s : SecP t.PP.L (pullback.fst t.G.hom y) j),
      ∃! c, Rep (pullback.snd t.G.hom y) (β R y hy) s c) :
    ∃ T' ≥ Ψ.T, ∀ (w : ℂ) (hw : Ψ.T < w.im), T' < w.im → ∃ σt : A.X → ((Fin A.gB → ℂ) → ℂ) → SecP t.PP.L (pullback.fst t.G.hom (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT)) j, (∀ α, ∀ th ∈ A.Theta j α, ∀ (q : Over.mk (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⟶ t.G) (q' : Over.mk y ⟶ t.G) jj, spMap (Γ.R w).val.toRingHom ≫ q.left = q'.left → ⊤ ≤ q.left ⁻¹ᵁ t.PP.L.U jj → ((sval (σt α th) (fib q) jj : Γ.R w) : ℂ⸨X⸩) = sval (Φ.sig j α th) (fib q') jj) ∧ ∃ σ₀ : A.X → ((Fin A.gB → ℂ) → ℂ) → SecP t.PP.L (pullback.fst t.G.hom (Ψ.yw w)) j, (∀ α th (q : Over.mk (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⟶ t.G) (q₀ : Over.mk (Ψ.yw w) ⟶ t.G) jj, q₀.left = spMap (Γ.ev w).toRingHom ≫ q.left → ⊤ ≤ q₀.left ⁻¹ᵁ t.PP.L.U jj → sval (σ₀ α th) (fib q₀) jj = Γ.ev w (sval (σt α th) (fib q) jj)) ∧ (∀ α, ∀ th ∈ A.Theta j α, ∀ v, HasVal (σ₀ α th) (fib (Ψ.pi w v)) (fun jj => Ψ.fr w jj v) (A.Sum j α th w v)) ∧ ∀ s : SecP t.PP.L (pullback.fst t.G.hom (Ψ.yw w)) j, ∃ (n : ℕ) (r : Fin n → ℂ) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ), (∀ i, th i ∈ A.Theta j (α i)) ∧ ∀ (q₀ : Over.mk (Ψ.yw w) ⟶ t.G) jj, ⊤ ≤ q₀.left ⁻¹ᵁ t.PP.L.U jj → sval s (fib q₀) jj = ∑ i, r i * sval (σ₀ (α i) (th i)) (fib q₀) jj := by
  have hb : ∀ {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') {z : Sp R ⟶ S} {z' : Sp R' ⟶ S}
      (hz : ⊤ ≤ z ⁻¹ᵁ V) (hz' : ⊤ ≤ z' ⁻¹ᵁ V) (q : Over.mk z ⟶ t.G) (q' : Over.mk z' ⟶ t.G) (i k),
      spMap ρ ≫ q.left = q'.left → ⊤ ≤ q.left ⁻¹ᵁ t.PP.L.U k →
      ArcPts.sval (β R' z' hz' i) (fib q') k = ρ (ArcPts.sval (β R z hz i) (fib q) k) := by
    intro R R' _ _ ρ z z' hz hz' q q' i k hq hk
    rw [← sval_spMap _ ρ _ (by rw [fib_fst]; exact hk)]
    refine hc _ _ _ _ _ _ _ _ _ i k (by rw [Category.assoc, fib_fst, fib_fst, hq]) ?_
    rw [fib_fst, ← hq]
    exact fun p _ => hk (x := spMap ρ p) trivial
  obtain ⟨T₂, a, ha, n, α, th, g, hth, hg⟩ := exists_coeff Φ hA (hβ _ y hy) fun i v c hv => by
    obtain ⟨x', hx'⟩ := hR.1 v
    obtain ⟨k, hk⟩ := exists_chart t.PP.isLB (Φ.x v).left
    have hy' : ⊤ ≤ (x' ≫ t.G.hom) ⁻¹ᵁ V := le_preimage_of_field (algebraMap Conv.convLaurent ℂ⸨X⸩) (by
      rw [← Category.assoc, hx', Over.w (Φ.x v)]; exact hy)
    have e := hb (algebraMap Conv.convLaurent ℂ⸨X⸩) hy' hy (Over.homMk x' rfl) (Φ.x v) i k hx'
      (le_preimage_of_field (algebraMap Conv.convLaurent ℂ⸨X⸩) (hx'.symm ▸ hk :))
    rw [hv k (by rw [fib_fst]; exact hk)] at e
    rw [eq_div_of_mul_eq (pow_ne_zero j ((Φ.frm v).1 k hk).ne_zero) e]
    exact div_mem (Subtype.property _) (pow_mem (hR.2 v k hk) j)
  obtain ⟨T₁, h₁, hT₁⟩ := Conv.exists_le_preimage_inclusion Ψ.yT (U := V)
    (le_preimage_of_field (algebraMap Conv.convLaurent ℂ⸨X⸩) (by
      rw [← Category.assoc, ← spMap_comp]
      exact Ψ.yT_gen.symm ▸ hy))
  obtain ⟨T₀, hT₀⟩ := A.exists_isConvLine
  refine ⟨max T₁ (max T₂ T₀), h₁.trans (le_max_left _ _), fun w hw hw' => ?_⟩
  obtain ⟨w₁, w₂, w₀⟩ : T₁ < w.im ∧ T₂ < w.im ∧ T₀ < w.im := by simpa only [max_lt_iff] using hw'
  have hyt : ⊤ ≤ (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⁻¹ᵁ V := by
    have e : (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom =
        (Subalgebra.inclusion (Γ.le T₁ w w₁)).toRingHom.comp
          (Subalgebra.inclusion (Conv.halfRing_mono h₁) : Conv.halfRing Ψ.T →+* Conv.halfRing T₁) := rfl
    rw [e, spMap_comp, Category.assoc]
    exact fun p _ => hT₁ (x := spMap _ p) trivial
  have hyw : ⊤ ≤ Ψ.yw w ⁻¹ᵁ V := by
    have e : (Conv.ev Ψ.T w hw).toRingHom =
        (Γ.ev w).toRingHom.comp (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom :=
      RingHom.ext fun r => (Γ.ev_eq _ _ hw r).symm
    rw [Ψ.yw_eq w hw, e, spMap_comp, Category.assoc]
    exact fun p _ => hyt (x := spMap _ p) trivial
  let i₂ := Subalgebra.inclusion (Γ.le T₂ w w₂)
  let σt := fun α th => comb (pullback.snd _ _) (fun i => i₂ (a α th i)) (β _ _ hyt)
  let σ₀ := fun α th => comb (pullback.snd _ _) (fun i => Γ.ev w (i₂ (a α th i))) (β _ _ hyw)
  have H₁ : ∀ α, ∀ th ∈ A.Theta j α,
      ∀ (q : Over.mk (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⟶ t.G) (q' : Over.mk y ⟶ t.G) k,
      spMap (Γ.R w).val.toRingHom ≫ q.left = q'.left → ⊤ ≤ q.left ⁻¹ᵁ t.PP.L.U k →
      ((ArcPts.sval (σt α th) (fib q) k : Γ.R w) : ℂ⸨X⸩) = ArcPts.sval (Φ.sig j α th) (fib q') k := by
    intro α th h q q' k hq hk
    rw [sval_comb _ _ _ _ _ (fib_snd q) (by rw [fib_fst]; exact hk), ha α th h _ _ _ k (fib_snd q')
      (by rw [fib_fst, ← hq]; exact fun p _ => hk (x := spMap _ p) trivial), AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun i _ => by rw [hb _ hyt hy q q' i k hq hk]; rfl
  have H₂ : ∀ α th (q : Over.mk (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⟶ t.G)
      (q₀ : Over.mk (Ψ.yw w) ⟶ t.G) k, q₀.left = spMap (Γ.ev w).toRingHom ≫ q.left → ⊤ ≤ q₀.left ⁻¹ᵁ t.PP.L.U k →
      ArcPts.sval (σ₀ α th) (fib q₀) k = Γ.ev w (ArcPts.sval (σt α th) (fib q) k) := by
    intro α th q q₀ k hq hk
    have hk' : ⊤ ≤ q.left ⁻¹ᵁ t.PP.L.U k := le_preimage_of_ev Γ w (hq ▸ hk :)
    rw [sval_comb _ _ _ _ _ (fib_snd q) (by rw [fib_fst]; exact hk'),
      sval_comb _ _ _ _ _ (fib_snd q₀) (by rw [fib_fst]; exact hk), map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hb _ hyt hyw q q₀ i k hq.symm hk', map_mul]; rfl
  refine ⟨σt, H₁, σ₀, H₂, fun α th h v k hk => ?_, fun s => ?_⟩
  · rw [fib_fst] at hk
    have hk' : ⊤ ≤ (Ψ.xt w hw v).left ⁻¹ᵁ t.PP.L.U k := le_preimage_of_ev Γ w (Ψ.pi_eq w hw v ▸ hk :)
    have hm : A.FSum j α th v ∈ Conv.halfRing T₀ := fun _ hw => (AnArc.hasSum_coeff_FSum hT₀ h hw v).summable
    have hs : Conv.ev T₀ w w₀ ⟨_, hm⟩ = A.Sum j α th w v :=
      Conv.ev_eq_of_hasSum w₀ _ (AnArc.hasSum_coeff_FSum hT₀ h w₀ v)
    have e : ArcPts.sval (σt α th) (fib (Ψ.xt w hw v)) k =
        Subalgebra.inclusion (Γ.le T₀ w w₀) ⟨_, hm⟩ * Ψ.τt w v k ^ j := by
      apply Subtype.ext
      rw [H₁ α th h _ _ k (Ψ.xt_gen w hw v) hk', Φ.val j α th h v k (by
        rw [fib_fst, ← Ψ.xt_gen w hw v]; exact fun p _ => hk' (x := spMap _ p) trivial), ← Ψ.τt_gen w hw v k hk']
      rfl
    rw [H₂ α th _ _ k (Ψ.pi_eq w hw v) hk, e, map_mul, map_pow, Γ.ev_eq T₀ w w₀, hs]
    rfl
  · obtain ⟨c, hc, -⟩ := hβ _ _ hyw s
    refine ⟨n, fun b => ∑ i, c i * Γ.ev w (i₂ (g i b)), α, th, hth, fun q₀ k hk => ?_⟩
    have hk' : ⊤ ≤ (fib q₀ ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U k := by rw [fib_fst]; exact hk
    have e : ∀ l, c l = ∑ b, (∑ i, c i * Γ.ev w (i₂ (g i b))) * Γ.ev w (i₂ (a (α b) (th b) l)) := fun l => by
      calc c l = ∑ i, c i * Γ.ev w (i₂ ((Pi.single i 1 : Fin N → _) l)) := by
            simp [Pi.single_apply, apply_ite]
        _ = _ := by
            simp only [← hg, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
            exact Finset.sum_comm
    have := (rep_comb (pullback.snd _ _) (fun b => σ₀ (α b) (th b)) fun b => ∑ i, c i * Γ.ev w (i₂ (g i b)))
    exact ((hc _ _ _ k (fib_snd q₀) hk').trans (by simp only [← e])).trans
      (((this.trans fun b => rep_comb _ _ _) _ _ _ k (fib_snd q₀) hk').symm.trans (this _ _ _ k (fib_snd q₀) hk'))

theorem sections_extend_and_span : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ (j : ℕ) [NeZero j], ∃ T' ≥ Ψ.T, ∀ (w : ℂ) (hw : Ψ.T < w.im), T' < w.im → ∃ σt : A.X → ((Fin A.gB → ℂ) → ℂ) → SecP o.t.PP.L (pullback.fst o.t.G.hom (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT)) j, (∀ α, ∀ th ∈ A.Theta j α, ∀ (q : Over.mk (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⟶ o.t.G) (q' : Over.mk y ⟶ o.t.G) jj, spMap (Γ.R w).val.toRingHom ≫ q.left = q'.left → ⊤ ≤ q.left ⁻¹ᵁ o.t.PP.L.U jj → ((sval (σt α th) (fib q) jj : Γ.R w) : ℂ⸨X⸩) = sval (Φ.sig j α th) (fib q') jj) ∧ ∃ σ₀ : A.X → ((Fin A.gB → ℂ) → ℂ) → SecP o.t.PP.L (pullback.fst o.t.G.hom (Ψ.yw w)) j, (∀ α th (q : Over.mk (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⟶ o.t.G) (q₀ : Over.mk (Ψ.yw w) ⟶ o.t.G) jj, q₀.left = spMap (Γ.ev w).toRingHom ≫ q.left → ⊤ ≤ q₀.left ⁻¹ᵁ o.t.PP.L.U jj → sval (σ₀ α th) (fib q₀) jj = Γ.ev w (sval (σt α th) (fib q) jj)) ∧ (∀ α, ∀ th ∈ A.Theta j α, ∀ v, HasVal (σ₀ α th) (fib (Ψ.pi w v)) (fun jj => Ψ.fr w jj v) (A.Sum j α th w v)) ∧ ∀ s : SecP o.t.PP.L (pullback.fst o.t.G.hom (Ψ.yw w)) j, ∃ (n : ℕ) (r : Fin n → ℂ) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ), (∀ i, th i ∈ A.Theta j (α i)) ∧ ∀ (q₀ : Over.mk (Ψ.yw w) ⟶ o.t.G) jj, ⊤ ≤ q₀.left ⁻¹ᵁ o.t.PP.L.U jj → sval s (fib q₀) jj = ∑ i, r i * sval (σ₀ (α i) (th i)) (fib q₀) jj := by
  intro hL _ E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ hA hR j _
  obtain ⟨V, hV, N, β, hc, hβ⟩ := exists_frame hL.secBaseChange (objPolAV o) j (NeZero.pos j)
    (y (default : PrimeSpectrum ℂ⸨X⸩))
  refine extend_of_frame Φ Γ Ψ hA hR j (V := V) (fun p _ => ?_) β hc hβ
  obtain rfl : p = (default : PrimeSpectrum ℂ⸨X⸩) := Subsingleton.elim (α := PrimeSpectrum ℂ⸨X⸩) _ _
  exact hV

end GlobalTheory.FibreFrame
