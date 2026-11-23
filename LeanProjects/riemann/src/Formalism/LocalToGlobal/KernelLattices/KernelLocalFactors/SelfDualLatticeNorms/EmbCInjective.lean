import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.KS

open Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker
open Formalism.L2.AlgTh (lamF flat vecE)
open Formalism.L2.Th1.GD (InMul)

variable {D : D7} {X : Fields} (s : Seam D X)

section Maps

variable {a b : ℕ}

def mat (x : HomE X.E a b) : Matrix (Fin b) (Fin a) D.host.E := fun i j => s.iE (x (Pi.single j 1) i)

def unmat (A : Matrix (Fin b) (Fin a) D.host.E) : HomE X.E a b := Matrix.toLin' (A.map s.iE.symm)

theorem mat_unmat (A : Matrix (Fin b) (Fin a) D.host.E) : mat s (unmat s A) = A := by
  funext i j
  simp [mat, unmat, Matrix.toLin'_apply]

theorem mat_mulVec (x : HomE X.E a b) (y : Sp X.E a) : (mat s x).mulVec (s.vec y) = s.vec (x y) := by
  funext i
  have h : x y = ∑ j, y j • x (Pi.single j 1) := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul]
    congr 1
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  show ∑ j, s.iE (x (Pi.single j 1) i) * s.iE (y j) = s.iE (x y i)
  rw [h, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_comm]

def phi (δ : ℂ) : HomE X.E a b →+ TaylorLogMetric.VC D a b where
  toFun x := fun τ i j => δ * TaylorLogMetric.embT D τ (s.iE (x (Pi.single j 1) i))
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp [mul_add]

def opM (e : D.host.E) : TaylorLogMetric.VC D a b →+ TaylorLogMetric.VC D a b where
  toFun v := fun τ i j => TaylorLogMetric.embT D τ e * v τ i j
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp [mul_add]

def emV : Matrix (Fin b) (Fin a) D.host.E →+ TaylorLogMetric.VC D a b where
  toFun A := fun τ i j => TaylorLogMetric.embT D τ (A i j)
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp

theorem embV_eq (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (A : Matrix (Fin b) (Fin a) D.host.E) :
    TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) A = emV A := rfl

theorem opM_smul (e : D.host.E) (w : ℂ) (v : TaylorLogMetric.VC D a b) : opM e (w • v) = w • opM e v := by
  funext τ i j
  show TaylorLogMetric.embT D τ e * (w * v τ i j) = w * (TaylorLogMetric.embT D τ e * v τ i j)
  ring

theorem emV_smulE (e : D.host.E) (A : Matrix (Fin b) (Fin a) D.host.E) : emV (e • A) = opM e (emV A) := by
  funext τ i j
  show TaylorLogMetric.embT D τ (e * A i j) = _
  rw [map_mul]
  rfl

theorem emV_smulO (r : 𝓞 D.host.E) (A : Matrix (Fin b) (Fin a) D.host.E) : emV (r • A) = opM (r : D.host.E) (emV A) := by
  funext τ i j
  show TaylorLogMetric.embT D τ (r • A i j) = _
  rw [Algebra.smul_def, map_mul]
  rfl

theorem phi_smulE (δ : ℂ) (e : X.E) (x : HomE X.E a b) : phi s δ (e • x) = opM (s.iE e) (phi s δ x) := by
  funext τ i j
  show δ * TaylorLogMetric.embT D τ (s.iE (e * x (Pi.single j 1) i)) = TaylorLogMetric.embT D τ (s.iE e) * (δ * _)
  rw [map_mul, map_mul]
  ring

theorem phi_smulO (δ : ℂ) (r : 𝓞 X.E) (x : HomE X.E a b) : phi s δ (r • x) = opM (s.iE (r : X.E)) (phi s δ x) := by
  funext τ i j
  show δ * TaylorLogMetric.embT D τ (s.iE (r • x (Pi.single j 1) i)) = TaylorLogMetric.embT D τ (s.iE (r : X.E)) * (δ * _)
  rw [Algebra.smul_def, map_mul, map_mul]
  show δ * (TaylorLogMetric.embT D τ (s.iE (r : X.E)) * _) = _
  ring

theorem phi_eq (δ : ℂ) (x : HomE X.E a b) : phi s δ x = δ • emV (mat s x) := rfl

end Maps

section Per

variable {a b : ℕ} (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

def aaX : Submodule (𝓞 X.E) X.E :=
  Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}

theorem La_stable (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (r : 𝓞 D.host.E) {v : TaylorLogMetric.VC D a b} (hv : v ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') :
    opM (r : D.host.E) v ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L' := by
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨w, hw, r • A, Submodule.smul_mem _ _ hA, ?_⟩
    rw [embV_eq, embV_eq, opM_smul, emV_smulO]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg x _ h => rw [map_neg]; exact neg_mem h

theorem mat_mem_hom {x : HomE X.E a b} (hx : x ∈ homO N N') : mat s x ∈ TaylorLogMetric.homL D (s.lat N) (s.lat N') := by
  refine Submodule.subset_span ?_
  intro y hy
  obtain ⟨y₀, hy₀, rfl⟩ := (s.mem_lat N y).1 hy
  rw [mat_mulVec]
  exact (s.mem_lat N' _).2 ⟨x y₀, hx y₀ hy₀, rfl⟩

theorem unmat_mem_hom {A : Matrix (Fin b) (Fin a) D.host.E} (hA : ∀ x ∈ s.lat N, A.mulVec x ∈ s.lat N') : unmat s A ∈ homO N N' := by
  intro y hy
  have h1 := hA (s.vec y) ((s.mem_lat N _).2 ⟨y, hy, rfl⟩)
  rw [← mat_unmat s A, mat_mulVec] at h1
  obtain ⟨z, hz, hzz⟩ := (s.mem_lat N' _).1 h1
  have : z = unmat s A y := by
    funext i
    exact s.iE.injective (congrFun hzz i)
  rw [← this]
  exact hz

theorem gen_eq (c : 𝓞 D.host.K) (t : D.host.E) (x : HomE X.E a b) :
    phi s δ (s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) • x) =
      (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • emV (t • mat s x) := by
  funext τ i j
  show δ * TaylorLogMetric.embT D τ (s.iE (s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) * x (Pi.single j 1) i)) =
    (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) * TaylorLogMetric.embT D τ (t * s.iE (x (Pi.single j 1) i))
  rw [map_mul, RingEquiv.apply_symm_apply, map_mul, map_mul, map_mul]
  have h := embOnK D τ (c : D.host.K)
  have h' : TaylorLogMetric.embT D τ (((c : D.host.K) : D.host.E)) = D.host.φ₀ (((c : D.host.K) : D.host.E)) := h
  rw [h']
  ring

theorem phi_mem_La {z : HomE X.E a b} (hz : z ∈ perO (aaX s cc) N N') :
    phi s δ z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') := by
  have key : ∀ r ∈ aaX s cc, ∀ x ∈ homO N N', phi s δ (r • x) ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem r h =>
      obtain ⟨c, hc, t, ht, rfl⟩ := h
      intro x hx
      rw [gen_eq]
      exact AddSubgroup.subset_closure ⟨_, AddSubgroup.subset_closure ⟨c, hc, rfl⟩, t • mat s x,
        Submodule.subset_span ⟨t, ht, mat s x, mat_mem_hom s N N' hx, rfl⟩, rfl⟩
    | zero => intro x _; rw [zero_smul, map_zero]; exact zero_mem _
    | add r r' _ _ h1 h2 => intro x hx; rw [add_smul, map_add]; exact add_mem (h1 x hx) (h2 x hx)
    | smul ρ r _ h =>
      intro x hx
      obtain ⟨ρ', hρ'⟩ := (s.int_iff (ρ : X.E)).2 ⟨ρ, rfl⟩
      rw [smul_assoc, phi_smulO, ← hρ']
      exact La_stable cc δ _ _ ρ' (h x hx)
  induction hz using Submodule.span_induction with
  | mem z h =>
    obtain ⟨r, hr, x, hx, rfl⟩ := h
    exact key r hr x hx
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul ρ z _ h =>
    obtain ⟨ρ', hρ'⟩ := (s.int_iff (ρ : X.E)).2 ⟨ρ, rfl⟩
    rw [phi_smulO, ← hρ']
    exact La_stable cc δ _ _ ρ' h

def imS : AddSubgroup (TaylorLogMetric.VC D a b) := (perO (aaX s cc) N N').toAddSubgroup.map (phi s δ)

theorem imS_stable (r : 𝓞 D.host.E) {v : TaylorLogMetric.VC D a b} (hv : v ∈ imS s cc δ N N') : opM (r : D.host.E) v ∈ imS s cc δ N N' := by
  obtain ⟨z, hz, rfl⟩ := hv
  obtain ⟨ρ, hρ⟩ := (s.int_iff (s.iE.symm (r : D.host.E))).1 ⟨r, by simp⟩
  refine ⟨ρ • z, Submodule.smul_mem _ _ hz, ?_⟩
  rw [phi_smulO]
  have : s.iE ((ρ : 𝓞 X.E) : X.E) = (r : D.host.E) := by
    have h2 : ((ρ : 𝓞 X.E) : X.E) = s.iE.symm (r : D.host.E) := hρ
    rw [h2, RingEquiv.apply_symm_apply]
  rw [this]

theorem La_le : TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ≤ imS s cc δ N N' := by
  have key4 : ∀ c ∈ cc, ∀ t ∈ D.host.AA0, ∀ A ∈ TaylorLogMetric.homL D (s.lat N) (s.lat N'),
      (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • emV (t • A) ∈ imS s cc δ N N' := by
    intro c hc t ht A hA
    induction hA using Submodule.span_induction with
    | mem A h =>
      refine ⟨s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) • unmat s A,
        Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, hc, t, ht, rfl⟩, unmat s A, unmat_mem_hom s N N' h, rfl⟩, ?_⟩
      rw [gen_eq, mat_unmat]
    | zero => rw [smul_zero, map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ h1 h2 => rw [smul_add, map_add, smul_add]; exact add_mem h1 h2
    | smul ρ A _ h =>
      rw [smul_comm, emV_smulO, ← opM_smul]
      exact imS_stable s cc δ N N' ρ h
  have key3 : ∀ c ∈ cc, ∀ A ∈ TaylorLogMetric.YYl D (s.lat N) (s.lat N'),
      (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • emV A ∈ imS s cc δ N N' := by
    intro c hc A hA
    induction hA using Submodule.span_induction with
    | mem A h =>
      obtain ⟨t, ht, A₀, hA₀, rfl⟩ := h
      exact key4 c hc t ht A₀ hA₀
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ h1 h2 => rw [map_add, smul_add]; exact add_mem h1 h2
    | smul ρ A _ h =>
      rw [emV_smulO, ← opM_smul]
      exact imS_stable s cc δ N N' ρ h
  have key2 : ∀ w ∈ TaylorLogMetric.lamOf D cc δ, ∀ A ∈ TaylorLogMetric.YYl D (s.lat N) (s.lat N'), w • emV A ∈ imS s cc δ N N' := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w h =>
      obtain ⟨c, hc, rfl⟩ := h
      exact key3 c hc
    | zero => intro A _; rw [zero_smul]; exact zero_mem _
    | add x y _ _ h1 h2 => intro A hA; rw [add_smul]; exact add_mem (h1 A hA) (h2 A hA)
    | neg x _ h => intro A hA; rw [neg_smul]; exact neg_mem (h A hA)
  unfold TaylorLogMetric.La
  rw [AddSubgroup.closure_le]
  rintro _ ⟨w, hw, A, hA, rfl⟩
  exact key2 w hw A hA

theorem phi_per : imS s cc δ N N' = TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact phi_mem_La s cc δ N N' hz
  · exact La_le s cc δ N N'

end Per

theorem embH_iff (hok : s.Ok) (δ : ℂ) {a b : ℕ} (x : HomE X.E a b) (z : DVar X.Tau a b → ℂ) :
    embH (X.embC s.σ₀) δ x = flat X.Tau a b z ↔ phi s δ x = s.flatV a b z := by
  constructor
  · intro h
    funext τ i j
    have h1 := congrFun (congrFun (congrFun h (s.iT.symm τ)) i) j
    have h2 : δ * s.σ₀ (X.emb (s.iT.symm τ) (x (Pi.single j 1) i)) = z (s.iT.symm τ, i, j) := h1
    rw [hok.1, Equiv.apply_symm_apply] at h2
    exact h2
  · intro h
    funext τ i j
    have h1 := congrFun (congrFun (congrFun h (s.iT τ)) i) j
    have h2 : δ * TaylorLogMetric.embT D (s.iT τ) (s.iE (x (Pi.single j 1) i)) = z (s.iT.symm (s.iT τ), i, j) := h1
    rw [← hok.1, Equiv.symm_apply_apply] at h2
    exact h2

theorem lamTie : LamTie := by
  intro D X s cc δ B χ cD a b N N' hok
  ext z
  have h1 : z ∈ lamF (ambOf s B χ cD) N N' ↔ ∃ x ∈ perO (aaX s cc) N N', embH (X.embC s.σ₀) δ x = flat X.Tau a b z := Iff.rfl
  have h2 : z ∈ s.laF B.tor (s.lat N) (s.lat N') ↔ s.flatV a b z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') := Iff.rfl
  rw [h1, h2, ← phi_per]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, (embH_iff s hok δ x z).1 h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, (embH_iff s hok δ x z).2 h⟩

section Frame

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

def unitM {a b : ℕ} (e : D.host.E) (β : Fin b) (α : Fin a) : Matrix (Fin b) (Fin a) D.host.E :=
  fun i j => if i = β ∧ j = α then e else 0

theorem unitM_mulVec {a b : ℕ} (e : D.host.E) (β : Fin b) (α : Fin a) (y : Fin a → D.host.E) :
    (unitM e β α).mulVec y = fun i => if i = β then e * y α else 0 := by
  funext i
  show ∑ j, (if i = β ∧ j = α then e else 0) * y j = _
  by_cases hi : i = β
  · simp [hi]
  · simp [hi]

theorem flatV_vecE (hok : s.Ok) {a b : ℕ} (n : ℕ) (ω : ℂ) (r : X.E) (β : Fin b) (α : Fin a) :
    s.flatV a b (ω • ((n : ℂ) • vecE s.σ₀ r β α)) = ω • emV (unitM ((n : D.host.E) * s.iE r) β α) := by
  funext τ i j
  show ω * ((n : ℂ) * (if i = β ∧ j = α then s.σ₀ (X.emb (s.iT.symm τ) r) else 0)) =
    ω * TaylorLogMetric.embT D τ (if i = β ∧ j = α then (n : D.host.E) * s.iE r else 0)
  by_cases h : i = β ∧ j = α
  · rw [if_pos h, if_pos h, hok.1, Equiv.apply_symm_apply, map_mul, map_natCast]
  · rw [if_neg h, if_neg h, map_zero, mul_zero]

theorem inMul_std (hok : s.Ok) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (p : ℕ) [hp : Fact p.Prime]
    (hN : s.StdAtP p N) (hN' : s.StdAtP p N') :
    ∃ n₀ : ℕ, ¬ p ∣ n₀ ∧ ∀ (r : 𝓞 X.E) (β : Fin b) (α : Fin a),
      InMul B.L (lamF (ambOf s B χ cD) N N') ((n₀ : ℂ) • vecE (ambOf s B χ cD).σ₀ (r : X.E) β α) := by
  obtain ⟨s₁, hs₁, -, h1b⟩ := hN
  obtain ⟨s₂, hs₂, h2a, -⟩ := hN'
  refine ⟨s₂ * s₁, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
    · exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hs₂.symm h
    · exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hs₁.symm h
  · intro r β α ω hω
    rw [lamTie D X s cc δ B χ cD a b N N' hok]
    show s.flatV a b (ω • (((s₂ * s₁ : ℕ) : ℂ) • vecE s.σ₀ (r : X.E) β α)) ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N')
    rw [flatV_vecE s hok]
    refine AddSubgroup.subset_closure ⟨ω, (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B ω).1 hω, _,
      Submodule.subset_span ⟨1, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.int_mem_inverse_half_different isIntegral_one, _, Submodule.subset_span ?_, (one_smul _ _).symm⟩, rfl⟩
    intro y hy
    rw [unitM_mulVec]
    obtain ⟨r', hr'⟩ := (s.int_iff (r : X.E)).2 ⟨r, rfl⟩
    have hy1 := h1b y hy
    unfold StandardLatticesGL3.stdL at hy1
    rw [Submodule.mem_pi] at hy1
    obtain ⟨u, hu⟩ := Submodule.mem_one.1 (hy1 α (Set.mem_univ _))
    have hv : (fun i => if i = β then s.iE (r : X.E) * ((s₁ : D.host.E) * y α) else 0 : Fin b → D.host.E) ∈ StandardLatticesGL3.stdL D b := by
      unfold StandardLatticesGL3.stdL
      rw [Submodule.mem_pi]
      intro i _
      by_cases hi : i = β
      · rw [if_pos hi]
        refine Submodule.mem_one.2 ⟨r' * u, ?_⟩
        rw [map_mul, hr', hu]
        rfl
      · rw [if_neg hi]
        exact zero_mem _
    have h3 := h2a _ hv
    have e : (fun i => if i = β then ((s₂ * s₁ : ℕ) : D.host.E) * s.iE (r : X.E) * y α else 0 : Fin b → D.host.E) =
        (s₂ : D.host.E) • (fun i => if i = β then s.iE (r : X.E) * ((s₁ : D.host.E) * y α) else 0 : Fin b → D.host.E) := by
      funext i
      by_cases hi : i = β
      · simp only [Pi.smul_apply, if_pos hi, smul_eq_mul]
        push_cast
        ring
      · simp only [Pi.smul_apply, if_neg hi, smul_zero]
    rw [e]
    exact h3

theorem embC_injective (hok : s.Ok) : Function.Injective (X.embC (ambOf s B χ cD).σ₀) := by
  intro τ τ' h
  apply s.iT.injective
  apply embInj D
  apply RingHom.ext
  intro y
  have h1 := congrArg (fun f : X.E →+* ℂ => f (s.iE.symm y)) h
  have h2 : s.σ₀ (X.emb τ (s.iE.symm y)) = s.σ₀ (X.emb τ' (s.iE.symm y)) := h1
  rw [hok.1, hok.1, RingEquiv.apply_symm_apply] at h2
  exact h2

theorem thF_eq {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    Formalism.L2.AlgTh.thF (ambOf s B χ cD) N N' = fun z => B.eNat χ a b (s.lat N) (s.lat N') (s.flatV a b z) := rfl

theorem frame_std (hF : Formalism.L2.AlgTh.KerFrame) (hok : s.Ok) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (hN : s.StdAtP p N) (hN' : s.StdAtP p N')
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr X.E) (hc : ∀ τ, ‖ι (cD τ)‖ ≤ 1) :
    ∃ (J : Type) (_ : Fintype J) (v : J → DVar X.Tau a b → ℂ) (M : J → DVar X.Tau a b → ℂ_[p]),
      (∀ j, InMul B.L (lamF (ambOf s B χ cD) N N') (v j)) ∧ (∀ j k, ‖M j k‖ ≤ 1) ∧
      ∀ i k, Formalism.L2.Th1.GD.frameM (ι : ℂ →+* ℂ_[p]) v M i k = if i = k then ι ((ambOf s B χ cD : Amb X).cD k.1) else 0 :=
  hF X (ambOf s B χ cD) a b N N' B.L p ι hdisc (embC_injective s B χ cD hok) (fun τ => hc (s.iT τ))
    (inMul_std s B χ cD hok N N' p hN hN')

end Frame

end Formalism.L2.Ker.KS
