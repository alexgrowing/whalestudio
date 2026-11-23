import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfiniteStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMuId

variable {D : D7} {a b r t n : ℕ}

scoped instance borelMx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩
scoped instance scMx (m n : ℕ) : SecondCountableTopology (Mx D m n) := (GlobalTheory.MixModel.lattice_Mx D m n).2.2.1

theorem fromCols_smul_apply (e : AE D) (x : Mx D a r) (v : Mx D a t) (i : Fin a) :
    ∀ k, Matrix.fromCols (e • x) (e • v) i k = e • Matrix.fromCols x v i k := by
  rintro (k | k) <;> rfl

theorem jn_smul (hn : r + t = n) (e : AE D) (x : Mx D a r) (v : Mx D a t) : jn hn (e • x) (e • v) = e • jn hn x v := by
  ext i j
  exact fromCols_smul_apply e x v i _

theorem jn_inl (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) (i : Fin a) (k : Fin r) :
    jn hn x v i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl k)) = x i k := by
  simp only [jn, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromCols_apply_inl]

theorem jn_inr (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) (i : Fin a) (k : Fin t) :
    jn hn x v i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr k)) = v i k := by
  simp only [jn, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromCols_apply_inr]

theorem intOff_jn (S : Finset (Pl D)) (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) :
    IntOff S (jn hn x v) ↔ IntOff S x ∧ IntOff S v := by
  constructor
  · intro h
    refine ⟨fun w hw i k => ?_, fun w hw i k => ?_⟩
    · simpa only [jn_inl] using h w hw i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl k))
    · simpa only [jn_inr] using h w hw i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr k))
  · rintro ⟨hx, hv⟩ w hw i j
    obtain ⟨k, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
    rcases k with k | k
    · rw [jn_inl]; exact hx w hw i k
    · rw [jn_inr]; exact hv w hw i k

theorem good_pos {S : Finset (Pl D)} {e : AE D} {Φ : Mx D a b → ℂ} (h : Good S e Φ) {x : Mx D a b} (hx : IntOff S x) :
    Φ x = Φ (e • x) := by
  rw [h x, if_pos hx]

theorem good_neg {S : Finset (Pl D)} {e : AE D} {Φ : Mx D a b → ℂ} (h : Good S e Φ) {x : Mx D a b} (hx : ¬ IntOff S x) :
    Φ x = 0 := by
  rw [h x, if_neg hx]

theorem continuous_jn (hn : r + t = n) : Continuous fun z : Mx D a r × Mx D a t => jn hn z.1 z.2 := by
  have h : Continuous fun z : Mx D a r × Mx D a t => Matrix.fromCols z.1 z.2 := by
    refine continuous_pi fun i => continuous_pi fun k => ?_
    rcases k with k | k
    · exact (continuous_apply k).comp ((continuous_apply i).comp continuous_fst)
    · exact (continuous_apply k).comp ((continuous_apply i).comp continuous_snd)
  exact h.matrix_submatrix _ _

theorem continuous_yv (V : HSp D) (b₀ : HermE D r) : Continuous fun z : Mx D V.rank r × Mx D V.rank t => yv V b₀ z :=
  continuous_const.matrix_mul ((continuous_adj.comp continuous_fst).matrix_mul (continuous_const.matrix_mul continuous_snd))

theorem measurable_sm (e : AE D) : Measurable fun z : Mx D a r × Mx D a t => (e • z.1, e • z.2) :=
  ((continuous_const_smul e).measurable.comp measurable_fst).prodMk ((continuous_const_smul e).measurable.comp measurable_snd)

theorem map_ne_zero (ν : Measure (Mx D a r × Mx D a t)) (s : Set (Mx D a r × Mx D a t)) (e : AE D) (hs : ν s ≠ 0) :
    (ν.restrict s).map (fun z => (e • z.1, e • z.2)) ≠ 0 := by
  intro h
  have := congrArg (fun μ : Measure _ => μ Set.univ) h
  simp only [Measure.map_apply (measurable_sm e) MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ,
    Measure.coe_zero, Pi.zero_apply] at this
  exact hs this

theorem transfer (hn : r + t = n) {V : HSp D} {b₀ : HermE D r} {S : Finset (Pl D)} {e : AE D}
    (ν : Measure (Mx D V.rank r × Mx D V.rank t))
    (hyv : ∀ z : Mx D V.rank r × Mx D V.rank t, IntOff S z.1 → IntOff S z.2 →
      IntOff S (yv V b₀ z) ∧ yv V b₀ (e • z.1, e • z.2) = e • yv V b₀ z)
    (Φ : Mx D V.rank n → ℂ) (η : Mx D r t → ℂ) (hΦc : Continuous Φ) (hηc : Continuous η) (hΦ : Good S e Φ)
    (hη : Good S e η) :
    ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv V b₀ z)) ∂((ν.restrict {z | IntOff S z.1 ∧ IntOff S z.2}).map
      fun z => (e • z.1, e • z.2)) = ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv V b₀ z)) ∂ν := by
  set F : Mx D V.rank r × Mx D V.rank t → ℂ := fun z => Φ (jn hn z.1 z.2) * conj (η (yv V b₀ z)) with hF
  set s : Set (Mx D V.rank r × Mx D V.rank t) := {z | IntOff S z.1 ∧ IntOff S z.2} with hs
  have hFc : Continuous F := (hΦc.comp (continuous_jn hn)).mul (Complex.continuous_conj.comp (hηc.comp (continuous_yv V b₀)))
  have hfc : Continuous fun z : Mx D V.rank r × Mx D V.rank t => (e • z.1, e • z.2) :=
    ((continuous_const_smul e).comp continuous_fst).prodMk ((continuous_const_smul e).comp continuous_snd)
  have key : ∀ z ∈ s, F (e • z.1, e • z.2) = F z := by
    rintro z ⟨h1, h2⟩
    obtain ⟨hy, hye⟩ := hyv z h1 h2
    have hj : IntOff S (jn hn z.1 z.2) := (intOff_jn S hn z.1 z.2).2 ⟨h1, h2⟩
    simp only [hF, hye, jn_smul]
    rw [← good_pos hΦ hj, ← good_pos hη hy]
  have off : ∀ z ∉ s, F z = 0 := by
    intro z hz
    have hj : ¬ IntOff S (jn hn z.1 z.2) := fun h => hz ((intOff_jn S hn z.1 z.2).1 h)
    simp only [hF, good_neg hΦ hj, zero_mul]
  rw [integral_map (measurable_sm e).aemeasurable hFc.aestronglyMeasurable]
  have hae : ∀ᵐ z ∂(ν.restrict s), F (e • z.1, e • z.2) = F z := by
    have hm : MeasurableSet {a : Mx D V.rank r × Mx D V.rank t | ¬F (e • a.1, e • a.2) = F a} :=
      (isOpen_ne_fun (hFc.comp hfc) hFc).measurableSet
    rw [ae_iff, Measure.restrict_apply hm]
    convert measure_empty (μ := ν)
    exact Set.eq_empty_iff_forall_notMem.2 fun z hz => hz.1 (key z hz.2)
  rw [integral_congr_ae hae, setIntegral_eq_integral_of_forall_compl_eq_zero off]

theorem orb_null {V : HSp D} {b₀ : HermE D r} {e : AE D} {ν : Measure (Mx D V.rank r × Mx D V.rank t)}
    (hν : IsOrb V b₀ e ν) (hfree : ν {z | ¬ Free e z} = 0)
    (hno : ∀ z : Mx D V.rank r × Mx D V.rank t, Free e z →
      ¬ (ip V z.1 z.1 = e • rat b₀.1 ∧ e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ qv V b₀ z = 0)) : ν = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  refine le_antisymm ?_ bot_le
  calc ν Set.univ ≤ ν ({z | ¬ (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0)} ∪
        {z | ¬ Free e z}) := by
        refine measure_mono fun z _ => ?_
        by_cases hz : Free e z
        · left
          rintro ⟨h1, h2, h3, h4⟩
          exact hno z hz ⟨h3, h1, h2, h4⟩
        · right; exact hz
    _ ≤ _ := measure_union_le _ _
    _ = 0 := by rw [hν.supp, hfree, add_zero]

end PositivityTheory.Rg.Rsw.L.LMuId

open PositivityTheory.Rg.Rsw.L.LMuId in
theorem PositivityTheory.Rg.Rsw.L.muId : IdemEx → GoodEv → BumpEx → ThProd → EisMeas → NullSing → Uniq → NoFrame → ThetaSideMeasure → ToS →
    MuId := by
  classical
  intro hI hG _ _ hE hN hU hF hT hS D n t B W d hn ψ χ θ μB μW ωB ωW hst mu hmu M m b₀ hb₀ hRho I
  have hdet : b₀.1.det ≠ 0 := hb₀.2
  have hθ : IsInfFam θ := hst.hθ
  obtain ⟨S₁, hS₁⟩ := hE D n t B W d hn ψ χ θ μB μW ωB ωW hst mu hmu M m b₀ hb₀ hRho
  have hΩc : ∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → Continuous (Ω 1) := fun Ω hΩ =>
    hΩ.cont.comp (continuous_const.prodMk continuous_id)
  refine ⟨?_, ?_⟩
  · intro hno Φ Ω hΩ hcs
    obtain ⟨S₂, hS₂⟩ := hF D t B W ⟨d⟩ b₀ hdet hno
    obtain ⟨S₃, hS₃⟩ := hG D θ hθ B.rank n Φ.1 Φ.2
    obtain ⟨S₄, hS₄⟩ := hG D θ hθ W.rank t (Ω 1) (hΩ.mem 1)
    set S := S₁ ∪ S₂ ∪ S₃ ∪ S₄ with hSdef
    obtain ⟨e, he⟩ := (hI D S).1
    obtain ⟨ν, hν, hint⟩ := hS₁ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he
    have h0 : ν = 0 := orb_null hν (hN D W.rank t B b₀ hdet S e he ν hν)
      (hS₂ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he)
    rw [hint Φ (hS₃ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he) Ω hΩ
      (hS₄ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he) hcs, h0, integral_zero_measure]
  · intro x₀ hx₀
    have : m.μ.IsAddHaarMeasure := m.hμ.1
    obtain ⟨ν₂, hν₂, ⟨S₅, hS₅⟩, hT2⟩ := hT D n t B W d hn I θ hθ m.μ inferInstance b₀ hdet x₀ hx₀
    obtain ⟨S₆, hS₆⟩ := hS D W.rank t B b₀ hdet
    have core : ∀ S, S₁ ⊆ S → S₅ ⊆ S → S₆ ⊆ S → ∀ e, IsIdem S e → ∃ c : ℂ, ∀ (Φ : schwartzA θ B.rank n) Ω,
        IsTh ψ χ θ b₀ m.μ Ω → HasCompactSupport (Ω 1) → Good S e Φ.1 → Good S e (Ω 1) →
        mu (Rsec M m ψ b₀ (fun g => (ωB g Φ).1 0) 1 Ω) =
          c * ∫ z, Φ.1 (jn hn z.1 z.2) * conj (Ω 1 (yv B b₀ z)) ∂ν₂ := by
      intro S h1 h5 h6 e he
      obtain ⟨ν, hν, hint⟩ := hS₁ S h1 e he
      obtain ⟨hOrb, hyv⟩ := hS₆ S h6 e he ν₂ hν₂
      obtain ⟨κ, hκ⟩ := hU D W.rank t B b₀ hdet S e he ν _ hν hOrb (map_ne_zero ν₂ _ e (hS₅ S h5))
      refine ⟨((κ : ℝ) : ℂ), fun Φ Ω hΩ hcs hΦg hΩg => ?_⟩
      rw [hint Φ hΦg Ω hΩ hΩg hcs, hκ, integral_smul_nnreal_measure,
        transfer hn ν₂ hyv Φ.1 (Ω 1) (GlobalTheory.T.schwartz_bound_finite_infinite D θ hθ _ _ Φ.1 Φ.2).1 (hΩc Ω hΩ) hΦg hΩg,
        NNReal.smul_def, Complex.real_smul]
    by_cases hex : ∃ (Φ₀ : schwartzA θ B.rank n) (Ω₀ : G D t → Mx D W.rank t → ℂ), IsTh ψ χ θ b₀ m.μ Ω₀ ∧
        HasCompactSupport (Ω₀ 1) ∧ ∫ z, Φ₀.1 (jn hn z.1 z.2) * conj (Ω₀ 1 (yv B b₀ z)) ∂ν₂ ≠ 0
    · obtain ⟨Φ₀, Ω₀, hΩ₀, hcs₀, hI₀⟩ := hex
      refine ⟨mu (Rsec M m ψ b₀ (fun g => (ωB g Φ₀).1 0) 1 Ω₀) /
        ∫ z, Φ₀.1 (jn hn z.1 z.2) * conj (Ω₀ 1 (yv B b₀ z)) ∂ν₂, fun Φ Ω hΩ hcs => ?_⟩
      obtain ⟨S₃, hS₃⟩ := hG D θ hθ B.rank n Φ.1 Φ.2
      obtain ⟨S₄, hS₄⟩ := hG D θ hθ W.rank t (Ω 1) (hΩ.mem 1)
      obtain ⟨S₇, hS₇⟩ := hG D θ hθ B.rank n Φ₀.1 Φ₀.2
      obtain ⟨S₈, hS₈⟩ := hG D θ hθ W.rank t (Ω₀ 1) (hΩ₀.mem 1)
      set S := S₁ ∪ S₅ ∪ S₆ ∪ S₃ ∪ S₄ ∪ S₇ ∪ S₈ with hSdef
      obtain ⟨e, he⟩ := (hI D S).1
      obtain ⟨c, hc⟩ := core S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he
      have h₀ := hc Φ₀ Ω₀ hΩ₀ hcs₀ (hS₇ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he) (hS₈ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he)
      have h := hc Φ Ω hΩ hcs (hS₃ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he) (hS₄ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he)
      have hcv : c = mu (Rsec M m ψ b₀ (fun g => (ωB g Φ₀).1 0) 1 Ω₀) /
          ∫ z, Φ₀.1 (jn hn z.1 z.2) * conj (Ω₀ 1 (yv B b₀ z)) ∂ν₂ := (eq_div_iff hI₀).mpr h₀.symm
      rw [h, ← hcv, (hT2 Φ.1 Φ.2 (Ω 1) (hΩ.mem 1)).2.2]
    · push Not at hex
      refine ⟨0, fun Φ Ω hΩ hcs => ?_⟩
      obtain ⟨S₃, hS₃⟩ := hG D θ hθ B.rank n Φ.1 Φ.2
      obtain ⟨S₄, hS₄⟩ := hG D θ hθ W.rank t (Ω 1) (hΩ.mem 1)
      set S := S₁ ∪ S₅ ∪ S₆ ∪ S₃ ∪ S₄ with hSdef
      obtain ⟨e, he⟩ := (hI D S).1
      obtain ⟨c, hc⟩ := core S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he
      rw [hc Φ Ω hΩ hcs (hS₃ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he) (hS₄ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he), hex Φ Ω hΩ hcs, mul_zero,
        zero_mul]

end
