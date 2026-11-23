import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueChernClassNilpotentBaseStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.FirstChernClassFactorial

theorem pow_dvd_factorial_mul (l : ℕ) (hl : 0 < l) (n : ℕ) : l ^ n ∣ (l * n).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (l * n).factorial * l.factorial ∣ (l * n + l).factorial :=
      Nat.factorial_mul_factorial_dvd_factorial_add _ _
    have h2 : l ∣ l.factorial := Nat.dvd_factorial hl le_rfl
    rw [pow_succ, Nat.mul_succ]
    exact (mul_dvd_mul ih h2).trans h1

theorem factorial_acr {l : ℕ} [Fact l.Prime] (n k : ℕ) (hk : l * n ≤ k) : (k.factorial : (PAlg.base l).Acr n) = 0 := by
  obtain ⟨a, ha⟩ := (pow_dvd_factorial_mul l (Fact.out : l.Prime).pos n).trans (Nat.factorial_dvd_factorial hk)
  rw [ha, Nat.cast_mul, Nat.cast_pow, (PAlg.base l).pow_l_acr n, zero_mul]

theorem dlog_eq_of_factorial {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) {N N' : ℕ} (h : N ≤ N')
    (hf : ∀ k, N ≤ k → (k.factorial : A) = 0) (v : A) : B.dlog δ N' v = B.dlog δ N v := by
  unfold B.dlog
  refine (Finset.sum_subset (Finset.range_mono h) fun k _ hk => ?_).symm
  rw [hf k (by simpa using hk)]
  simp

open B in

theorem isFirstChern_base_change {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b b' : Base}
    {ht : b.t = 1} {ht' : b'.t = 1} {κ : O →+* b.R ⧸ b.I} {κ' : O →+* b'.R ⧸ b'.I}
    (σ : b.R →+* b'.R) (hp : b.p = b'.p) (hI : IsDPMorphism b.γ b'.γ σ) (τ : b.R ⧸ b.I →+* b'.R ⧸ b'.I)
    (hτ : τ.comp κ = κ') (hτσ : ∀ r, τ (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (σ r))
    {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (c' : Λ →+* b'.R) (hc : ∀ a, σ (c a) = c' (RingHom.id Λ a))
    (D : E.LineData X) {N N' : ℕ} (hN : N ≤ N') (hf : ∀ k, N ≤ k → (k.factorial : b'.R) = 0)
    (y : CH.H (OM ((schFn q).cr b ht κ) c) 2)
    (hy : IsFirstChernClassOfLineBundle (q := q) (b := b) (ht := ht) (κ := κ) D c N' y) :
    IsFirstChernClassOfLineBundle (q := q) (b := b') (ht := ht') (κ := κ') D c' N
      ((omMor (crMor (F := schFn q) (F' := schFn q) (b := b) (b' := b') (ht := ht) (ht' := ht') σ hp hI
        (basePt (schFn q) τ hτ) fun _ y r => congrArg y.1.1 (hτσ r)) (RingHom.id Λ) hc).pull 2 y) := by
  intro C _ G Lf
  let mm := omMor (c := c) (c' := c') (crMor (F := schFn q) (F' := schFn q) (b := b) (b' := b') (ht := ht) (ht' := ht') σ hp hI
        (basePt (schFn q) τ hτ) fun _ y r => congrArg y.1.1 (hτσ r)) (RingHom.id Λ) hc
  let G' : C ⥤ Thick ((schFn q).cr b ht κ) := G ⋙ mm.G
  let Lf' : CLift G' D := { p := Lf.p, hp := Lf.hp, w := Lf.w, hw := Lf.hw }
  obtain ⟨hz', hcl⟩ := hy C G' Lf'
  let m4 : CH.Mor (G' ⋙ OM _ c) (G ⋙ OM _ c') (RingHom.id _) :=
    { G := 𝟭 C, τ := fun T => mm.τ (G.obj T), nat := fun φ x => mm.nat (G.map φ) x }
  have hE : m4.pullC 2 (Lf'.coc c N') = Lf.coc c' N := by
    funext s
    refine dlog_eq_of_factorial (G.obj (s.obj (Fin.last 2))).δ hN (fun j hj => ?_) _
    have := congrArg (G.obj (s.obj (Fin.last 2))).i (hf j hj)
    rw [map_natCast, map_zero] at this
    exact this
  have hz : CH.d _ 2 (Lf.coc c' N) = 0 := by
    rw [← hE, m4.d_pullC, hz', map_zero]
  refine ⟨hz, ?_⟩
  have h1 : (CH.Mor.restrict (OM _ c') G).pull 2 (mm.pull 2 y) =
      m4.pull 2 ((CH.Mor.restrict (OM _ c) G').pull 2 y) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rfl
  refine Eq.trans ?_ h1.symm
  rw [← hcl]
  have key : ∀ (z : CH.Cn (G ⋙ OM _ c') 2) (h : CH.d _ 2 z = 0), z = Lf.coc c' N →
      (CH.cx _).cls z h = (CH.cx _).cls (Lf.coc c' N) hz := by
    rintro _ _ rfl
    rfl
  exact (key (m4.pullC 2 (Lf'.coc c N')) (by rw [m4.d_pullC, hz', map_zero]) hE).symm

open B in

theorem chern_class_reduction_compatible {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l) (k : Bool)
    (D : E.LineData X) (n : ℕ) (y : B.Hc (schFn q) κ k (n + 1) 2)
    (hy : IsFirstChernClassOfLineBundle (q := q) (b := bs l k (n + 1)) (ht := rfl) (κ := κb κ k (n + 1)) D ((PAlg.base l).cris (n + 1)) (l * (n + 1)) y) :
    IsFirstChernClassOfLineBundle (q := q) (b := bs l k n) (ht := rfl) (κ := κb κ k n) D ((PAlg.base l).cris n) (l * n)
      (redHc (schFn q) κ k n.le_succ 2 y) :=
  isFirstChern_base_change (b := bs l k (n + 1)) (b' := bs l k n) ((PAlg.base l).red n.le_succ) rfl (dd_red k _ n.le_succ)
    (Ideal.quotientMap _ _ (red_le k n.le_succ)) (red_κb κ k n.le_succ) (fun _ => rfl) _ _ (red_cris _ n.le_succ) D
    (Nat.mul_le_mul_left l n.le_succ) (fun j hj => factorial_acr n j hj) y hy

theorem exists_C1H {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (D : E.LineData M.X)
    (hD : sSup (𝒱D D) = ⊤) : ∃ x : (M.HS false 2).lim, B.IsFirstChernFamily M.p D (okToOC l K) false x.1 := by
  have ex : ∀ n, ∃! x, B.IsFirstChernClassOfLineBundle (q := M.p) (b := B.bs l false n) (ht := rfl) (κ := B.κb (okToOC l K) false n) D
      ((PAlg.base l).cris n) (l * n) x := fun n =>
    GlobalTheory.T.existsUnique_chern_class_nilpotent_base (B.DD false (PAlg.base l) n) l (Fact.out : l.Prime).ne_zero M.p (B.κb (okToOC l K) false n) D hD
      ((PAlg.base l).cris n) (l * n) (factorial_acr n _ le_rfl)
  choose x hx hu using ex
  refine ⟨⟨x, fun n => ?_⟩, hx⟩
  exact hu n _ (chern_class_reduction_compatible M.p (okToOC l K) false D n (x (n + 1)) (hx (n + 1)))

end GlobalTheory.CompanionTheory.FirstChernClassFactorial
