import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelCoinvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind

noncomputable section

namespace GlobalTheory.ThK.Partner

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.BigNZ
open scoped TensorProduct Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Pair

variable {n d : ℕ} {X : Spc F E n} {Y : Spc F E d}

theorem pure_smul (c : ℂ) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) :
    pure (c • f) φ = c • pure f φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

theorem polData_sum {B : Base F E} {M : Model σ X Y} {Φ} (h : Φ ∈ PolData B M) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol B.ψ B.emb ∧ Fam M (φ i)) ∧ Φ = ∑ i, pure (f i) (φ i) := by
  obtain ⟨m, c, g, e⟩ := Submodule.mem_span_set'.1 h
  choose f hf φ hφ hv hΦ using fun i => (g i).2
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hv i⟩, ?_⟩
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pure_smul, ← hΦ i]

theorem finite_bad {M : Model σ X Y} {m : ℕ} {φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ}
    (h : ∀ i, Fam M (φ i)) : {v | ∃ i, φ i v ≠ M.vac v}.Finite := by
  have e : {v | ∃ i, φ i v ≠ M.vac v} = ⋃ i, {v | φ i v ≠ M.vac v} := by ext; simp
  rw [e]
  exact Set.finite_iUnion fun i => eventually_cofinite.1 (h i).2

end Pair

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem partner_of_big (hK : KP) (hM : IsMatched B G X om om' R Rf) {Φ} (hΦ : Φ ∈ PolData B G.M) :
    ∃ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' := by
  have hco : Coinv B G X om om' Rf := GlobalTheory.T.theta_kernel_coinvariant hK.base F E σ B a a' G X om om' R Rf hM
  obtain ⟨m, f, φ, hfφ, rfl⟩ := polData_sum hΦ
  have hfin := finite_bad fun i => (hfφ i).2
  let T : Finset (Pl F) := X.T ∪ {B.v₁} ∪ hfin.toFinset
  have hXT : X.T ⊆ T := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have h1 : B.v₁ ∈ T := Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hout : ∀ i, ∀ v ∉ T, φ i v = G.M.vac v := fun i v hv => by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 ⟨i, hc⟩))
  have hre : ∀ i, ∃ g ∈ G.M'.Pol B.ψ B.emb, R.p' g = R.p (f i) := fun i =>
    Submodule.mem_map.1 (hM.real.quot'.onto ▸ Submodule.mem_top)
  choose f' hf' ef using hre
  have hsb : ∀ i v, ∃ χ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v χ = Rf.p v (φ i v) := fun i v =>
    Submodule.mem_map.1 ((hM.fin.onto' v).symm ▸ Submodule.mem_top)
  choose χ hχ eχ using hsb
  have hso : ∀ i, ∃ ζ ∈ G.M'.SoLoc B.ψ B.τ₁, Rf.p' B.v₁ ζ = Rf.p B.v₁ (φ i B.v₁) := fun i =>
    (hco.1 B.v₁ hM.triple.chars.good).2.2.1 B.τ₁ _
  choose ζ hζ eζ using hso
  let φ₀ : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ := fun i v => if v ∈ T then χ i v else G.M'.vac v
  let φ' : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ := fun i => Function.update (φ₀ i) B.v₁ (ζ i)
  have fam₀ : ∀ i, Fam G.M' (φ₀ i) := fun i => by
    refine ⟨fun v => ?_, T.eventually_cofinite_notMem.mono fun v hv => if_neg hv⟩
    by_cases hv : v ∈ T
    · simp only [φ₀, if_pos hv]; exact hχ i v
    · simp only [φ₀, if_neg hv]; exact (hM.triple.geo.hM'.vac v).1
  have fam' : ∀ i, Fam G.M' (φ' i) := fun i => (fam₀ i).update B.v₁ (hζ i).1
  have out' : ∀ i, ∀ v ∉ T, φ' i v = G.M'.vac v := fun i v hv => by
    have hne : v ≠ B.v₁ := fun e => hv (e ▸ h1)
    simp only [φ', Function.update_of_ne hne, φ₀, if_neg hv]
  refine ⟨∑ i, pure (f' i) (φ' i), Submodule.sum_mem _ fun i _ => Submodule.subset_span
    ⟨f' i, φ' i, (fam' i).1, (fam' i).2, by simp only [φ', Function.update_self]; exact hζ i, rfl⟩, ?_⟩
  refine ⟨T, hXT, m, m, f, φ, f', φ', fun i => ⟨(hfφ i).1, (hfφ i).2.1, hout i⟩,
    fun i => ⟨hf' i, (fam' i).1, out' i⟩, rfl, rfl, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ef i]
  congr 2
  funext ⟨v, hvT⟩
  by_cases hv : v = B.v₁
  · subst hv
    simp only [φ', Function.update_self, eζ]
  · simp only [φ', Function.update_of_ne hv, φ₀, if_pos hvT, eχ]

theorem partner_of_small (hM : IsMatched B G X om om' R Rf) {Φ'} (hΦ' : Φ' ∈ PolData B G.M') :
    ∃ Φ, PolMatch B G X R Rf Φ Φ' := by
  obtain ⟨m, f', φ', hfφ, rfl⟩ := polData_sum hΦ'
  have hfin := finite_bad fun i => (hfφ i).2
  let T : Finset (Pl F) := X.T ∪ hfin.toFinset
  have hXT : X.T ⊆ T := Finset.subset_union_left
  have hout : ∀ i, ∀ v ∉ T, φ' i v = G.M'.vac v := fun i v hv => by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 ⟨i, hc⟩))
  have hre : ∀ i, ∃ g ∈ G.M.Pol B.ψ B.emb, R.p g = R.p' (f' i) := fun i =>
    Submodule.mem_map.1 (hM.real.quot.onto ▸ Submodule.mem_top)
  choose f hf ef using hre
  have hsb : ∀ i v, ∃ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf.p v χ = Rf.p' v (φ' i v) := fun i v =>
    Submodule.mem_map.1 ((hM.fin.onto v).symm ▸ Submodule.mem_top)
  choose χ hχ eχ using hsb
  let φ : Fin m → ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ := fun i v => if v ∈ T then χ i v else G.M.vac v
  have hφ : ∀ i v, φ i v ∈ SB _ := fun i v => by
    by_cases hv : v ∈ T
    · simp only [φ, if_pos hv]; exact hχ i v
    · simp only [φ, if_neg hv]; exact (hM.triple.geo.hM.vac v).1
  refine ⟨∑ i, pure (f i) (φ i), T, hXT, m, m, f, φ, f', φ', fun i => ⟨hf i, hφ i, fun v hv => if_neg hv⟩,
    fun i => ⟨(hfφ i).1, (hfφ i).2.1, hout i⟩, rfl, rfl, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ef i]
  congr 2
  funext ⟨v, hvT⟩
  simp only [φ, if_pos hvT, eχ]

theorem match_of_polMatch (hM : IsMatched B G X om om' R Rf) {Φ Φ'} (hS : Φ' ∈ G.M'.So B.ψ B.τ₁)
    (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ PolData B G.M ∧ Φ' ∈ PolData B G.M' ∧ Match B G X R Rf Φ Φ' := by
  obtain ⟨T, -, m, m', f, φ, f', φ', hi, hj, e1, e2, -⟩ := id h
  have fam : ∀ i, Fam G.M (φ i) := fun i => ⟨(hi i).2.1, T.eventually_cofinite_notMem.mono (hi i).2.2⟩
  have fam' : ∀ j, Fam G.M' (φ' j) := fun j => ⟨(hj j).2.1, T.eventually_cofinite_notMem.mono (hj j).2.2⟩
  refine ⟨e1 ▸ Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (hi i).1, φ i, (fam i).1, (fam i).2, rfl⟩,
    e2 ▸ Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨f' j, (hj j).1, φ' j, (fam' j).1, (fam' j).2, rfl⟩,
    hS, m, m', fun i => finPartFn (φ i), f, fun _ => f, fun j => finPartFn (φ' j), f', fun _ => f',
    fun i => ⟨(fam i).sb hM.triple.geo.hM, tendsto_const_nhds⟩, fun j => ⟨(fam' j).sb hM.triple.geo.hM', tendsto_const_nhds⟩,
    e1, e2, fun _ => ⟨?_, ?_⟩⟩
  · show ∑ j, pure (f' j) (φ' j) ∈ _
    rw [← e2]; exact hS
  · show PolMatch B G X R Rf (∑ i, pure (f i) (φ i)) (∑ j, pure (f' j) (φ' j))
    rw [← e1, ← e2]; exact h

end GlobalTheory.ThK.Partner

namespace GlobalTheory.ThK

theorem matchEx_of_classicalTheorems (hK : KP) : MatchEx := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hM
  exact ⟨fun Φ hΦ => Partner.partner_of_big hK hM hΦ, fun Φ' hΦ' => Partner.partner_of_small hM hΦ',
    fun Φ Φ' hS h => Partner.match_of_polMatch hM hS h⟩

end GlobalTheory.ThK

end
