import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MomT

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable

section Inputs

open Formalism.MainNotions.TaylorLogMetric

def goodLifts (D : D7) (T : Tor D) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    AddSubgroup (VC D N N') :=
  AddSubgroup.closure {y | ∃ κ : 𝓞 D.host.K,
    ‖lamC lam (D.host.φ₀ (D.host.conj ((κ : D.host.K) : D.host.E)))‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧
    ∃ x ∈ La D T L L', y = (D.host.φ₀ ((κ : D.host.K) : D.host.E) * (N₀ : ℂ) / (p : ℂ) ^ n) • x}

def MomentsAt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (Ω : ℂ_[p]) : Prop :=
  ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' → ∀ t : VC D N N', TorsPrime D p (La D (tor0 D cc δ) L L') t →
    ∃ N₀ : ℕ, Nat.Coprime N₀ p ∧
    ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), NNBasis D (tor0 D cc δ) δ p L L' b →
    ∃ μ : C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p], ‖μ‖ ≤ 1 ∧
      ∀ (n : ℕ), ∀ y ∈ goodLifts D (tor0 D cc δ) lam N₀ n L L',
        CoefIn D (Wop D (tor0 D cc δ) p y (U D (tor0 D cc δ) t (e N N' L L'))) Qbar ∧
        ∀ (m : ℕ) (y' : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[p], ℂ_[p])),
          (∀ a : Fin r → ℕ, g (fun i => (a i : ℤ_[p])) =
            lamC lam (kap D (tor0 D cc δ) (δ • embV D (tor0 D cc δ) (∑ i, (a i : D.host.E) • b i)) y) *
              ∏ j, pairN D lam Ω b (y' j) fun i => (a i : ℤ_[p])) →
          jet D lam y' (pSer D lam (Wop D (tor0 D cc δ) p y (U D (tor0 D cc δ) t (e N N' L L')))) = μ g

def TranslateMoments (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    (p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) → Nat.Coprime (Ideal.absNorm cc) p →
    ∃ Ω : ℂ_[p], IsOmP lam (tor0 D cc δ).abelian₂ Ω ∧ MomentsAt D cc δ e lam Ω

def TranslateMomentsAll : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → TranslateMoments D cc δ (B.eNat χ)

def MovesAll : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ

def LatticeFactsAll : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ), X.Ok → s.Ok → IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ →
    ∀ a b : ℕ, Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ ∧ (ambOf s B χ cD).ESmooth a b

end Inputs

section Ops

variable {X : Fields} (A : Amb X) {a b : ℕ}

def emb (x : HomE X.E a b) : VCx X.Tau a b := embH (X.embC A.σ₀) A.δ x

def Wx (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ) : VCx X.Tau a b → ℂ :=
  fun z => alV A.d A.sc (emb A x) * opU (HV A.sc) (emb A x) F z

def imH (x y : HomE X.E a b) : ℝ := altE (HV A.sc) (emb A x) (emb A y)

def coc (x y : HomE X.E a b) : ℝ := (Real.sqrt A.d * (HV A.sc (emb A x) (emb A y)).re + imH A x y) / 2

def brkE (y t : HomE X.E a b) : ℂ := brk (HV A.sc) (emb A y) (emb A t)

abbrev per (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Submodule (𝓞 X.E) (HomE X.E a b) :=
  perO A.AA N N'

def smulLat (r : X.E) (M : Submodule (𝓞 X.E) (HomE X.E a b)) : Submodule (𝓞 X.E) (HomE X.E a b) :=
  M.map ((r • (LinearMap.id : HomE X.E a b →ₗ[X.E] HomE X.E a b)).restrictScalars (𝓞 X.E))

theorem mem_smulLat (r : X.E) (M : Submodule (𝓞 X.E) (HomE X.E a b)) (y : HomE X.E a b) :
    y ∈ smulLat r M ↔ ∃ m ∈ M, r • m = y := Iff.rfl

variable (a b) in

def PtMom {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]) (v : X.E) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    ∀ t : HomE X.E a b, (∃ n : ℕ, Nat.Coprime n p ∧ (n : X.E) • t ∈ per A N N') →
    ∃ N₀ : ℕ, Nat.Coprime N₀ p ∧
      (∀ y ∈ per A N N', ∀ m, jetC A.cD (Wx A (((N₀ : X.E) * v) • y) (Wx A t (A.e a b N N'))) m ∈ TaylorLogMetric.Qbar) ∧
      InIntClosure (per A N N' : Set (HomE X.E a b))
        (fun x (k : HomE X.E a b × (DVar X.Tau a b →₀ ℕ)) =>
          TaylorLogMetric.lamC lam (brkE A (((N₀ : X.E) * v) • k.1) x) * ptTab ι un x k.2)
        {k | k.1 ∈ per A N N'}
        fun k => TaylorLogMetric.lamC lam (jetC A.cD (Wx A (((N₀ : X.E) * v) • k.1) (Wx A t (A.e a b N N'))) k.2)

variable (a b) in

def Ctx (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p g cA : ℕ) : Prop :=
  X.Ok ∧ A.LaHyp a b S ∧ A.AAUnit (divs (X.conjO ϖ)) ∧ A.ESmooth a b ∧ p.Prime ∧ ϖ * X.conjO ϖ = (p : 𝓞 X.E) ∧
    IsCoprime ϖ (X.conjO ϖ) ∧ (∀ P, P ∈ S ↔ ϖ ∈ P.asIdeal ∨ P ∈ SG) ∧ (∀ P ∈ SG, (p : 𝓞 X.E) ∉ P.asIdeal) ∧
    Nat.Coprime g p ∧ Nat.Coprime cA p

end Ops

section Clo

variable {p : ℕ} [Fact p.Prime] {H I : Type}

theorem clo_zero (Sup : Set H) (tab : H → I → ℂ_[p]) (M : Set I) : InIntClosure Sup tab M fun _ => 0 := by
  intro F _ ε hε
  exact ⟨0, by simp, by simp, by simpa using fun _ _ => hε⟩

theorem clo_add {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} {J J' : I → ℂ_[p]}
    (h : InIntClosure Sup tab M J) (h' : InIntClosure Sup tab M J') : InIntClosure Sup tab M fun m => J m + J' m := by
  classical
  intro F hF ε hε
  obtain ⟨c, hc, hc1, hcF⟩ := h F hF ε hε
  obtain ⟨c', hc', hc1', hcF'⟩ := h' F hF ε hε
  refine ⟨c + c', ?_, fun x => ?_, fun m hm => ?_⟩
  · intro x hx
    rcases Finset.mem_union.1 (Finsupp.support_add (Finset.mem_coe.1 hx)) with h | h
    exacts [hc h, hc' h]
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc1 x) (hc1' x))
  · rw [Finsupp.sum_add_index' (by simp) (by intros; ring)]
    have : J m + J' m - ((c.sum fun x r => r * tab x m) + c'.sum fun x r => r * tab x m) =
        (J m - c.sum fun x r => r * tab x m) + (J' m - c'.sum fun x r => r * tab x m) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hcF m hm) (hcF' m hm))

theorem clo_sum {κ : Type} {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} (s : Finset κ) (J : κ → I → ℂ_[p])
    (h : ∀ k ∈ s, InIntClosure Sup tab M (J k)) : InIntClosure Sup tab M fun m => ∑ k ∈ s, J k m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using clo_zero Sup tab M
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact clo_add (h k (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem clo_congr {Sup Sup' : Set H} {tab : H → I → ℂ_[p]} {M M' : Set I} {J J' : I → ℂ_[p]}
    (h : InIntClosure Sup tab M J) (hS : Sup ⊆ Sup') (hM : M' ⊆ M) (hJ : ∀ m ∈ M', J' m = J m) :
    InIntClosure Sup' tab M' J' := by
  intro F hF ε hε
  obtain ⟨c, hc, hc1, hcF⟩ := h F (hF.trans hM) ε hε
  exact ⟨c, hc.trans hS, hc1, fun m hm => by rw [hJ m (hF hm)]; exact hcF m hm⟩

theorem clo_comb {I' κ : Type} {Sup Sup' : Set H} {tab : H → I → ℂ_[p]} {tab' : H → I' → ℂ_[p]} {M : Set I} {M' : Set I'}
    {J : I → ℂ_[p]} (h : InIntClosure Sup tab M J) (s : Finset κ) (r : κ → I' → ℂ_[p]) (φ : κ → I' → I)
    (hφ : ∀ k ∈ s, ∀ m ∈ M', φ k m ∈ M) (w : H → ℂ_[p]) (hw : ∀ x ∈ Sup, ‖w x‖ ≤ 1) (hw0 : ∀ x ∈ Sup, x ∉ Sup' → w x = 0)
    (htab : ∀ x ∈ Sup, ∀ m ∈ M', ∑ k ∈ s, r k m * tab x (φ k m) = w x * tab' x m) :
    InIntClosure Sup' tab' M' fun m => ∑ k ∈ s, r k m * J (φ k m) := by
  classical
  intro F hF ε hε
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ k ∈ s, ∀ m ∈ F, ‖r k m‖ ≤ C := by
    refine ⟨1 + ∑ q ∈ s ×ˢ F, ‖r q.1 q.2‖, by positivity, fun k hk m hm => ?_⟩
    have := Finset.single_le_sum (f := fun q : κ × I' => ‖r q.1 q.2‖) (fun _ _ => norm_nonneg _)
      (Finset.mk_mem_product hk hm)
    linarith
  obtain ⟨c, hc, hc1, hcF⟩ := h ((s ×ˢ F).image fun q => φ q.1 q.2) (by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hi)
    exact hφ _ (Finset.mem_product.1 hq).1 _ (hF (Finset.mem_product.1 hq).2)) (ε / 2 / C) (by positivity)
  have hmem : ∀ x, c x ≠ 0 → x ∈ Sup := fun x hx => hc (Finsupp.mem_support_iff.2 hx)
  refine ⟨Finsupp.onFinset c.support (fun x => c x * w x) (fun x hx => Finsupp.mem_support_iff.2 (left_ne_zero_of_mul hx)),
    ?_, fun x => ?_, fun m hm => ?_⟩
  · intro x hx
    have hx' : c x * w x ≠ 0 := by simpa using hx
    by_contra hn
    exact hx' (by rw [hw0 x (hmem x (left_ne_zero_of_mul hx')) hn, mul_zero])
  · rw [Finsupp.onFinset_apply]
    by_cases hx : c x = 0
    · simp [hx]
    · rw [norm_mul]; exact mul_le_one₀ (hc1 x) (norm_nonneg _) (hw x (hmem x hx))
  · rw [Finsupp.onFinset_sum _ (by simp)]
    have e : ∑ k ∈ s, r k m * J (φ k m) - ∑ x ∈ c.support, c x * w x * tab' x m =
        ∑ k ∈ s, r k m * (J (φ k m) - c.sum fun x q => q * tab x (φ k m)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finsupp.sum, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [mul_assoc, ← htab x (hc hx) m (hF hm), Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (C := ε / 2) (by positivity) fun k hk => ?_)
      (by linarith)
    rw [norm_mul]
    have h1 := hcF (φ k m) (Finset.mem_image.2 ⟨(k, m), Finset.mk_mem_product hk hm, rfl⟩)
    calc _ ≤ C * (ε / 2 / C) := mul_le_mul (hC k hk m hm) h1.le (norm_nonneg _) hC0.le
      _ = ε / 2 := by field_simp

theorem clo_smul {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} {J : I → ℂ_[p]} (h : InIntClosure Sup tab M J)
    (r c : ℂ_[p]) (hc : c ≠ 0) (hr : ‖r‖ ≤ ‖c‖) :
    InIntClosure Sup (fun x m => c * tab x m) M fun m => r * J m := by
  have := clo_comb (Sup' := Sup) (tab' := fun x m => c * tab x m) (M' := M) h ({()} : Finset Unit) (fun _ _ => r) (fun _ m => m)
    (fun _ _ _ hm => hm) (fun _ => r / c)
    (fun _ _ => by rw [norm_div]; exact div_le_one_of_le₀ hr (norm_nonneg _)) (fun _ h h' => absurd h h')
    (fun x _ m _ => by simp only [Finset.sum_singleton]; field_simp)
  simpa using this

theorem clo_mul {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} {J : I → ℂ_[p]} (h : InIntClosure Sup tab M J)
    (r : ℂ_[p]) (hr : ‖r‖ ≤ 1) : InIntClosure Sup tab M fun m => r * J m := by
  simpa using clo_smul h r 1 one_ne_zero (by simpa using hr)

end Clo

end GlobalTheory.MomT
