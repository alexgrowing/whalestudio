import Development.WeilBound.ThetaLifts.LocalTheory.MemPolData

noncomputable section

namespace PositivityTheory.ThKG.Loc

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF
open scoped Classical

structure Hyp2 : Prop where
  meas : MeasEx
  floc : FLocB
  bumpA : BumpA
  bumpB : BumpB
  runiq : RealUniq
  unr : UnramifiedMultiplicityOneProportional
  ram : RamifiedMultiplicityOne
  inf : ArchimedeanMultiplicityOne
  ctBZ : CTBigZero
  ctSC : CTSmallCone
  ctBC : CTBigCone
  ctSZ : CTSmallZero

variable {B : Base F E}

def wT (B : Base F E) (X : Chars F E) (s : ℤˣ) (z : ℤ) (v : Pl F) : ℂ :=
  if h : v ∈ B.P then (chrW X.ν (B.τ ⟨v, h⟩) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps B.ψ (chrW X.ν (B.τ ⟨v, h⟩)) z else 0

theorem stepFac_eq {X : Chars F E} (h : X.T ⊆ B.P) (e₁ e₂ s : ℤˣ) (𝔟 𝔠) (z : ℤ) : stepFac B X e₁ e₂ s 𝔟 𝔠 z =
    ((idealVal X.ν 𝔟 ^ (e₁ : ℤ) * idealVal X.ν 𝔠 ^ (e₂ : ℤ) : ℂˣ) : ℂ) * ∏ v ∈ X.T, wT B X s z v := by
  unfold stepFac
  congr 1
  refine Finset.prod_bij (fun v _ => v.1) (fun v hv => by simpa using hv) (fun _ _ _ _ e => Subtype.ext e)
    (fun v hv => ⟨⟨v, h hv⟩, by simpa using hv, rfl⟩) fun v _ => ?_
  rw [wT, dif_pos v.2]

theorem prod_w {T₀ T : Finset (Pl F)} (h : T₀ ⊆ T) (w u : Pl F → ℂ) :
    ∏ v ∈ T, (if v ∈ T₀ then w v else u v) = (∏ v ∈ T₀, w v) * ∏ v ∈ T \ T₀, u v := by
  rw [← Finset.prod_sdiff h, mul_comm]
  congr 1
  · exact Finset.prod_congr rfl fun v hv => if_pos hv
  · exact Finset.prod_congr rfl fun v hv => if_neg (Finset.mem_sdiff.1 hv).2

theorem nu_eq {X X' : Chars F E} {a a' : ℕ} (h : X.IsGood B a a') (h' : X'.IsGood B a a') (l : (AE F E)ˣ)
    (hl : At (evI F) ((l : AE F E) - 1)) : X.ν l = X'.ν l := by
  have e1 : X.α l = X'.α l := Subtype.ext ((h.expα l hl).trans (h'.expα l hl).symm)
  have e2 : X.β l = X'.β l := Subtype.ext ((h.expβ l hl).trans (h'.expβ l hl).symm)
  simp only [Chars.ν, MonoidHom.div_apply, e1, e2]

theorem hasExp_div {χ χ' : Chr F E} {k k'} (h : HasExp B.emb χ k) (h' : HasExp B.emb χ' k') : HasExp B.emb (χ / χ') (k - k') := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => (zpow_sub₀ ?_ _ _).symm
  have : piInf (B.emb w) z ≠ 0 := (z.isUnit.map _).ne_zero
  exact div_ne_zero this (by exact_mod_cast norm_ne_zero_iff.2 this)

theorem cone_sum {κ κ' ι : Type} [Fintype κ] [Fintype ι] {c : ((κ → AF F) → ℂ) → (κ' → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, ∀ a : ℂ, c (Φ + a • Ψ) = c Φ + a • c Ψ) (Φ : ι → (κ → AF F) → ℂ) (hΦ : ∀ i, Φ i ∈ schA F κ) :
    c (∑ i, Φ i) = ∑ i, c (Φ i) := by
  have z : c 0 = 0 := by
    have := h 0 (zero_mem _) 0 (zero_mem _) 1
    simpa using this
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using z
  | insert i s hi ih =>
    have := h _ (hΦ i) _ (Submodule.sum_mem _ fun j (_ : j ∈ s) => hΦ j) 1
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih, ← one_smul ℂ (∑ j ∈ s, Φ j), this, one_smul, one_smul]

theorem pure_smul {κ : Type} [Fintype κ] (c : ℂ) (a : SInf F κ) (φ) : pure (c • a) φ = c • pure a φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem ex_p_ne {A P : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P] [Nontrivial P] {p : A →ₗ[ℂ] P} {S : Submodule ℂ A}
    (h : S.map p = ⊤) : ∃ x ∈ S, p x ≠ 0 := by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : P)
  obtain ⟨f, hf, e⟩ := Submodule.mem_map.1 (h ▸ Submodule.mem_top : ξ ∈ S.map p)
  exact ⟨f, hf, e ▸ hξ⟩

theorem one_const {ι A : Type*} (Dat : ι → Prop) (Co : ι → A → Prop) (Rel : A → ℂ → Prop) (Out : ι → ℂ → Prop)
    (h1 : ∀ i, Dat i → ∃ L c, c ≠ 0 ∧ Co i L ∧ Rel L c ∧ Out i c) (h2 : ∀ i j L L', Dat i → Dat j → Co i L → Co j L' → L = L')
    (h3 : ∀ i, Dat i → ∀ L c c', Rel L c → Rel L c' → c = c') : ∃ c, c ≠ 0 ∧ ∀ i, Dat i → Out i c := by
  by_cases h : ∃ i, Dat i
  · obtain ⟨i, hi⟩ := h
    obtain ⟨L, c, hc, a, b, -⟩ := h1 i hi
    refine ⟨c, hc, fun j hj => ?_⟩
    obtain ⟨L', c', -, a', b', o⟩ := h1 j hj
    obtain rfl := h2 i j L L' hi hj a a'
    rwa [h3 i hi L c c' b b']
  · exact ⟨1, one_ne_zero, fun i hi => absurd ⟨i, hi⟩ h⟩

end PositivityTheory.ThKG.Loc

end
