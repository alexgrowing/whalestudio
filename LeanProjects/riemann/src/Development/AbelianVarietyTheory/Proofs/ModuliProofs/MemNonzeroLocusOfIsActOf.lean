import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsGenOfInvariant

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoprimeTorsion

open CommutatorPairing

section General

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (T : Over S)

def chartPullLPow (n : ℕ) : ChartPull (LPow A L n T) (lbPow L n) (snd T A).left where
  idx j := fun _ => j 0
  le j y hy := mem_powChart.2 (Set.mem_iInter.1 hy 0)
  g y j j' hj hj' := by
    refine (gm_linComb L (fun _ : Fin 1 => (snd T A).left) (fun _ => (n : ℤ)) (𝟙 _) y j j' hj hj').trans
      (Eq.trans ?_ (gm_lbPow_g n (snd T A).left y _ _ (mem_powChart.2 (Set.mem_iInter.1 hj 0))
        (mem_powChart.2 (Set.mem_iInter.1 hj' 0))).symm)
    rw [Fin.prod_univ_one, Category.id_comp, zpow_natCast]

theorem nonzeroLocus_chartPullLPow (n : ℕ) (s : (lbPow L n).Sec) :
    nonzeroLocus (chartSec (chartPullLPow A L T n) s) = (snd T A).left ⁻¹ᵁ nonzeroLocus s :=
  nonzeroLocus_chartSec _ s fun _ J hJ => ⟨fun _ => J PUnit.unit, Set.mem_iInter.2 fun _ => mem_powChart.1 hJ⟩

def vanishing (a : ℤ) (E : Set (T ⊗ A).left) : Submodule Γ(T.left, ⊤) (SecM A L a T) where
  carrier := {f | ∀ y ∈ E, y ∉ nonzeroLocus (SecM.toSec A f)}
  add_mem' := by
    intro f f' hf hf' y hy h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    rcases Scheme.basicOpen_add_le _ (f.1 k) (f'.1 k) hk with h | h
    · exact hf y hy (Opens.mem_iSup.2 ⟨k, h⟩)
    · exact hf' y hy (Opens.mem_iSup.2 ⟨k, h⟩)
  zero_mem' := by
    intro y _ h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    exact (Scheme.basicOpen_zero _ _).le hk
  smul_mem' := by
    intro c f hf y hy h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    exact hf y hy (Opens.mem_iSup.2 ⟨k, ((Scheme.basicOpen_mul _ (liftHom A _ c) (f.1 k)).le hk).2⟩)

variable {A L T}

theorem mem_nonzeroLocus_of_isActOf (hL : L.IsLB) {a : ℤ} {θ : ThetaGrp A L a T} {s s' : LB.Sec (LPow A L a T)}
    (h : IsActOf A L a θ s s') {y : (T ⊗ A).left} (hy : y ∈ nonzeroLocus s') :
    (translT A θ.pt).left y ∈ nonzeroLocus s := by
  obtain ⟨k, hk, hu⟩ := (mem_nonzeroLocus s' y).1 hy
  obtain ⟨i, hi⟩ := exists_chart hL ((translPt A θ.pt).left y)
  obtain ⟨i₀, rfl⟩ : ∃ i₀ : L.ι, k = fun _ => i₀ := ⟨k 0, funext fun b => congrArg k (Subsingleton.elim _ _)⟩
  have hm : y ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] ![i₀, i] := Set.mem_iInter.2 fun b => by
    fin_cases b
    exacts [Set.mem_iInter.1 hk 0, hi]
  have hp := chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) ![i₀, i] hm
  have e := (gs_res (𝟙 _) y _ hm _).symm.trans ((congrArg (gs (𝟙 _) y _) (h ![i₀, i])).trans
    ((gs_mul (𝟙 _) y _ hm _ _).trans (congrArg (_ * ·) ((gs_res (𝟙 _) y _ hm _).trans
      (gs_pull (𝟙 _) (translT A θ.pt).left y _ hp _)))))
  have u := isUnit_of_mul_isUnit_right ((congrArg IsUnit e).mp hu)
  rw [Category.id_comp] at u
  exact (mem_nonzeroLocus_iff_pull s (translT A θ.pt).left y (k := fun _ => i) hp).2 u

end General

theorem dense_torsion (hA : AmpleSt) (hK : KerPowSt) (hI : IrredSt) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P : PolAV (Sp k)) {p : ℕ} (hp : p.Prime) :
    Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ P.A | ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ x ^ n = 1}, Set.range x.left) := by
  haveI : IsCommMonObj P.A := P.isAb.comm
  rw [dense_iff_inter_open]
  rintro U hU ⟨y₀, hy₀⟩
  by_contra hne
  obtain ⟨a, -, s, hs, hle, -⟩ := (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample).exists_affine_le
    (U := ⟨U, hU⟩) hy₀
  have gen : ∀ N : ℕ, 4 ≤ N → ∀ y : P.A.left, ∃ t : (lbPow P.L N).Sec, y ∈ nonzeroLocus t := fun N hN y => by
    obtain ⟨m, t, ht, -⟩ := veryAmple_lbPow hA k P N hN
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
    exact ⟨t i, hi⟩
  obtain ⟨m, hm, hmp⟩ : ∃ m : ℕ, 4 ≤ m ∧ m.Coprime p :=
    ⟨p * 2 + 1, by have := hp.two_le; omega, by simp⟩
  obtain ⟨t, ht⟩ := gen m hm y₀
  let n := a * p + m
  have hn : 4 ≤ n := le_add_left hm
  have hnp : n.Coprime p := by simpa [n] using hmp
  let σ : (lbPow P.L n).Sec := secMul (secPow s p) t
  have hσ : nonzeroLocus σ = nonzeroLocus s ⊓ nonzeroLocus t := by
    rw [nonzeroLocus_secMul, nonzeroLocus_secPow s hp.one_le]
  let B := baseOver (Sp k)
  let β : ∀ T : Over (Sp k), T ⟶ B := fun T => Over.homMk T.hom (Category.comp_id _)
  let E : Set (B ⊗ P.A).left := ⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ P.A | ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ x ^ n = 1},
    Set.range (lift (β _) x).left
  have hsnd : ∀ {T : Over (Sp k)} (x : T ⟶ P.A) (z : T.left), (snd B P.A).left ((lift (β T) x).left z) = x.left z :=
    fun x z => congrArg (fun q => q.left z) (lift_snd (β _) x)
  rcases hI k P n (Or.inr hn) (Nat.cast_ne_zero.2 (by omega)) (vanishing P.A P.L B n E) (fun θ r r' hr h y hy hy' => by
      refine h _ ?_ (mem_nonzeroLocus_of_isActOf P.isLB hr hy')
      obtain ⟨x, ⟨l, hl, hlp, hx⟩, z, rfl⟩ := Set.mem_iUnion₂.1 hy
      have hθ : θ.pt ^ n = 1 := (hK _ P n (by omega) B θ.pt).1 fun q =>
        ⟨⊤, trivial, exists_isGen_pull _ θ.φ θ.isGen _⟩
      refine Set.mem_iUnion₂.2 ⟨(β _ ≫ θ.pt) * x, ⟨n * l, by positivity, Nat.Coprime.mul_left hnp hlp, ?_⟩, z,
        (congrArg (fun q => q.left z) (lift_translT θ.pt (β _) x)).symm⟩
      rw [mul_pow, pow_mul, pow_mul', hx, ← MonObj.comp_pow, hθ, MonObj.comp_one, one_pow, one_pow,
        _root_.mul_one]) with h | h
  · have hmem : SecM.ofSec P.A (chartSec (chartPullLPow P.A P.L B n) σ) ∈ vanishing P.A P.L B n E := fun y hy hy' => by
      obtain ⟨x, hx, z, rfl⟩ := Set.mem_iUnion₂.1 hy
      have h₁ : (snd B P.A).left ((lift (β _) x).left z) ∈ nonzeroLocus σ :=
        (nonzeroLocus_chartPullLPow P.A P.L B n σ).le hy'
      rw [hsnd, hσ] at h₁
      exact hne ⟨_, hle h₁.1, Set.mem_iUnion₂.2 ⟨x, hx, z, rfl⟩⟩
    rw [h, Submodule.mem_bot] at hmem
    have h₂ : (lift (β _) (𝟙 P.A)).left y₀ ∈ nonzeroLocus (chartSec (chartPullLPow P.A P.L B n) σ) :=
      (nonzeroLocus_chartPullLPow P.A P.L B n σ).ge (show (snd B P.A).left _ ∈ nonzeroLocus σ by
        rw [hsnd, hσ]; exact ⟨hs, ht⟩)
    exact (hmem ▸ (vanishing P.A P.L B n Set.univ).zero_mem :
      SecM.ofSec P.A (chartSec (chartPullLPow P.A P.L B n) σ) ∈ vanishing P.A P.L B n Set.univ) _ trivial h₂
  · let z : (𝟙_ (Over (Sp k))).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
    obtain ⟨τ, hτ⟩ := gen n hn ((1 : 𝟙_ (Over (Sp k)) ⟶ P.A).left z)
    have hmem : SecM.ofSec P.A (chartSec (chartPullLPow P.A P.L B n) τ) ∈ vanishing P.A P.L B n E := by
      rw [h]; trivial
    refine hmem ((lift (β _) 1).left z) (Set.mem_iUnion₂.2 ⟨1, ⟨1, one_pos, by simp, one_pow _⟩, z, rfl⟩)
      ((nonzeroLocus_chartPullLPow P.A P.L B n τ).ge ?_)
    show (snd B P.A).left _ ∈ nonzeroLocus τ
    rw [hsnd]; exact hτ

end GlobalTheory.CoprimeTorsion
