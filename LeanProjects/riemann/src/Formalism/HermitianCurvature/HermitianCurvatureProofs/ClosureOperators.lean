import Formalism.HermitianCurvature.CapelliDeterminantAndBranching

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.ClosureOperators

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def Cl {N : ℕ} (E : Fin N → Fin N → Module.End ℂ V) (L : Fin N → Fin N → Prop) (M : Submodule ℂ V) :
    Submodule ℂ V :=
  sInf {P | M ≤ P ∧ ∀ a b, L a b → ∀ q ∈ P, E a b q ∈ P}

theorem le_Cl {N : ℕ} (E : Fin N → Fin N → Module.End ℂ V) (L : Fin N → Fin N → Prop) (M : Submodule ℂ V) :
    M ≤ Cl E L M := le_sInf fun _ hP => hP.1

theorem Cl_closed {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} {L : Fin N → Fin N → Prop} {M : Submodule ℂ V}
    (a b : Fin N) (h : L a b) (q : V) (hq : q ∈ Cl E L M) : E a b q ∈ Cl E L M := by
  unfold Cl at hq ⊢
  rw [Submodule.mem_sInf] at hq ⊢
  intro P hP
  exact hP.2 a b h q (hq P hP)

theorem Cl_le {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} {L : Fin N → Fin N → Prop} {M : Submodule ℂ V}
    (P : Submodule ℂ V) (h1 : M ≤ P) (h2 : ∀ a b, L a b → ∀ q ∈ P, E a b q ∈ P) : Cl E L M ≤ P :=
  sInf_le ⟨h1, h2⟩

theorem gen {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} (hE : GlRel E) (T L : Fin N → Fin N → Prop)
    (M : Submodule ℂ V)
    (h0 : ∀ a b, T a b → ∀ m ∈ M, E a b m ∈ Cl E L M)
    (h1 : ∀ a b c d, T a b → L c d → b = c → T a d ∨ L a d)
    (h2 : ∀ a b c d, T a b → L c d → d = a → T c b ∨ L c b) :
    ∀ a b, T a b → ∀ q ∈ Cl E L M, E a b q ∈ Cl E L M := by
  have key : Cl E L M ≤ Cl E L M ⊓ ⨅ a, ⨅ b, ⨅ (_ : T a b), (Cl E L M).comap (E a b) := by
    apply Cl_le
    · intro m hm
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
      exact ⟨le_Cl E L M hm, fun a b hab => h0 a b hab m hm⟩
    · intro c d hcd q hq
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hq ⊢
      obtain ⟨hq1, hq2⟩ := hq
      refine ⟨Cl_closed c d hcd q hq1, fun a b hab => ?_⟩
      have hc := hE a b c d
      have e : E a b (E c d q) = E c d (E a b q) +
          ((if b = c then E a d else 0) - (if d = a then E c b else 0)) q := by
        rw [← hc]
        simp only [LinearMap.sub_apply, Module.End.mul_apply]
        abel
      rw [e]
      refine Submodule.add_mem _ (Cl_closed c d hcd _ (hq2 a b hab)) ?_
      rw [LinearMap.sub_apply]
      refine Submodule.sub_mem _ ?_ ?_
      · split_ifs with hbc
        · rcases h1 a b c d hab hcd hbc with h | h
          · exact hq2 a d h
          · exact Cl_closed a d h q hq1
        · simp
      · split_ifs with hda
        · rcases h2 a b c d hab hcd hda with h | h
          · exact hq2 c b h
          · exact Cl_closed c b h q hq1
        · simp
  intro a b hab q hq
  have hk := key hq
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hk
  exact hk.2 a b hab

theorem mono_succ {n : ℕ} (f : Fin (n + 1) → Module.End ℂ V) (a : Fin (n + 1) → ℕ) :
    mono f a = f 0 ^ a 0 * mono (fun x => f x.succ) (fun x => a x.succ) := by
  simp only [mono, List.ofFn_succ, List.prod_cons]

theorem mono_zero : ∀ {n : ℕ} (f : Fin n → Module.End ℂ V), mono f (fun _ => 0) = 1 := by
  intro n
  induction n with
  | zero => intro f; simp [mono]
  | succ k ih =>
    intro f
    rw [mono_succ]
    simp only [pow_zero, one_mul]
    exact ih _

theorem mul_mono : ∀ {n : ℕ} (f : Fin n → Module.End ℂ V), (∀ a b, f a * f b = f b * f a) →
    ∀ (a : Fin n → ℕ) (x : Fin n), ∃ a' : Fin n → ℕ, f x * mono f a = mono f a' := by
  intro n
  induction n with
  | zero => intro f _ a x; exact x.elim0
  | succ k ih =>
    intro f hf a x
    cases x using Fin.cases with
    | zero =>
      refine ⟨Fin.cons (a 0 + 1) (fun y => a y.succ), ?_⟩
      rw [mono_succ, mono_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [pow_succ', mul_assoc]
    | succ y =>
      obtain ⟨a'', h''⟩ := ih (fun z => f z.succ) (fun p q => hf _ _) (fun z => a z.succ) y
      refine ⟨Fin.cons (a 0) a'', ?_⟩
      rw [mono_succ, mono_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← mul_assoc, ((show Commute (f y.succ) (f 0) from hf _ _).pow_right (a 0)).eq, mul_assoc, h'']

def MS {n : ℕ} (f : Fin n → Module.End ℂ V) (v : V) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range fun a : Fin n → ℕ => mono f a v)

theorem mem_MS {n : ℕ} (f : Fin n → Module.End ℂ V) (v : V) : v ∈ MS f v := by
  apply Submodule.subset_span
  exact ⟨fun _ => 0, by simp [mono_zero]⟩

theorem MS_closed {n : ℕ} (f : Fin n → Module.End ℂ V) (hf : ∀ a b, f a * f b = f b * f a) (v : V) (x : Fin n) :
    ∀ p ∈ MS f v, f x p ∈ MS f v := by
  intro p hp
  have hle : MS f v ≤ (MS f v).comap (f x) := by
    unfold MS
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨a', ha'⟩ := mul_mono f hf a x
    show f x (mono f a v) ∈ Submodule.span ℂ (Set.range fun a : Fin n → ℕ => mono f a v)
    rw [show f x (mono f a v) = (f x * mono f a) v from rfl, ha']
    exact Submodule.subset_span ⟨a', rfl⟩
  exact hle hp

theorem MS_le_ker {n : ℕ} (f : Fin n → Module.End ℂ V) (v : V) (ξ : Module.Dual ℂ V)
    (h : ∀ a : Fin n → ℕ, ξ (mono f a v) = 0) : MS f v ≤ LinearMap.ker ξ := by
  unfold MS
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact LinearMap.mem_ker.mpr (h a)

theorem yK_comm {n : ℕ} {E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V} (hE : GlRel E) (a b : Fin n) :
    yK E a * yK E b = yK E b * yK E a := by
  have h := hE (Fin.last n) a.castSucc (Fin.last n) b.castSucc
  rw [if_neg (Fin.castSucc_lt_last a).ne, if_neg (Fin.castSucc_lt_last b).ne, sub_zero] at h
  exact sub_eq_zero.mp h

theorem etaK_comm {n : ℕ} {E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V} (hE : GlRel E) (a b : Fin n) :
    etaK E a * etaK E b = etaK E b * etaK E a := by
  have h := hE a.castSucc (Fin.last n) b.castSucc (Fin.last n)
  rw [if_neg (Fin.castSucc_lt_last b).ne', if_neg (Fin.castSucc_lt_last a).ne', sub_zero] at h
  exact sub_eq_zero.mp h

theorem exists_castSucc {n : ℕ} (a : Fin (n + 1)) (h : a ≠ Fin.last n) : ∃ a' : Fin n, a = a'.castSucc := by
  first
  | exact ⟨a.castPred h, (Fin.castSucc_castPred a h).symm⟩
  | (obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr h; exact ⟨j, hj.symm⟩)

theorem top_of_stab {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} (hI : Irr E) (S : Submodule ℂ V) (hS : Stab E S)
    (v : V) (hv : v ∈ S) (hv0 : v ≠ 0) : S = ⊤ := by
  refine (hI.2 S hS).resolve_left (fun h => hv0 ?_)
  rw [h] at hv
  exact (Submodule.mem_bot ℂ).mp hv

theorem trace_comm {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} (hE : GlRel E) (a b : Fin N) :
    (∑ c, E c c) * E a b = E a b * ∑ c, E c c := by
  rw [Finset.sum_mul, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun c _ => hE c c a b), Finset.sum_sub_distrib]
  simp

theorem trace_scalar [FiniteDimensional ℂ V] {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} (hE : GlRel E)
    (hI : Irr E) : ∃ ζ : ℂ, ∀ v : V, (∑ c, E c c) v = ζ • v := by
  haveI := hI.1
  obtain ⟨ζ, hζ⟩ := Module.End.exists_eigenvalue (∑ c, E c c)
  refine ⟨ζ, fun v => ?_⟩
  have hS : Stab E (LinearMap.ker ((∑ c, E c c) - ζ • 1)) := by
    intro a b w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have e := congrArg (fun g : Module.End ℂ V => g w) (trace_comm hE a b)
    simp only [Module.End.mul_apply] at e
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hw ⊢
    rw [e, sub_eq_zero.mp hw, map_smul, sub_self]
  obtain ⟨w, hw⟩ := hζ.exists_hasEigenvector
  have hmem : w ∈ LinearMap.ker ((∑ c, E c c) - ζ • 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    exact hw.apply_eq_smul
  have htop := top_of_stab hI _ hS w hmem hw.2
  have hv : v ∈ LinearMap.ker ((∑ c, E c c) - ζ • 1) := by rw [htop]; trivial
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hv
  exact hv

end Formalism.FourierDecayAlt.P.ClosureOperators

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr ClosureOperators

private theorem MS_le_of_mem_of_invariant {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (f : Fin n → Module.End ℂ V)
    (v : V) (P : Submodule ℂ V) (hv : v ∈ P) (hf : ∀ x, ∀ q ∈ P, f x q ∈ P) : MS f v ≤ P := by
  have key : ∀ (k : ℕ) (g : Fin k → Module.End ℂ V), (∀ x, ∀ q ∈ P, g x q ∈ P) →
      ∀ b : Fin k → ℕ, mono g b v ∈ P := by
    intro k
    induction k with
    | zero =>
      intro g _ b
      have h1 : mono g b = 1 := by simp [mono]
      rw [h1]
      exact hv
    | succ k ih =>
      intro g hg b
      rw [mono_succ, Module.End.mul_apply]
      have h2 := ih (fun x => g x.succ) (fun x q hq => hg x.succ q hq) (fun x => b x.succ)
      generalize b 0 = j
      induction j with
      | zero => rw [pow_zero, Module.End.one_apply]; exact h2
      | succ j ihj => rw [pow_succ', Module.End.mul_apply]; exact hg 0 _ ihj
  unfold MS
  rw [Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  exact key n f hf b

theorem span_top_vectors : Qr.SpanTop := by
  intro V _ _ n E ν v₀ hE hI hW hv0 ξ hξ hm
  let L : Fin (n + 1) → Fin (n + 1) → Prop := fun a b => a ≠ Fin.last n ∧ b ≠ Fin.last n ∧ b < a
  let M : Submodule ℂ V := MS (yK E) v₀
  have hyc : ∀ a b, yK E a * yK E b = yK E b * yK E a := yK_comm hE
  have hMC : M ≤ Cl E L M := le_Cl E L M
  have hv₀M : v₀ ∈ M := mem_MS (yK E) v₀
  have hNL : ∀ b, ¬ L (Fin.last n) b := fun b h => h.1 rfl
  have hY : ∀ (x : Fin n), ∀ q ∈ Cl E L M, E (Fin.last n) x.castSucc q ∈ Cl E L M := by
    intro x q hq
    refine gen hE (fun a b => a = Fin.last n ∧ b ≠ Fin.last n) L M ?_ ?_ ?_ _ _
      ⟨rfl, (Fin.castSucc_lt_last x).ne⟩ q hq
    · rintro a b ⟨rfl, hb⟩ m hm'
      obtain ⟨b', rfl⟩ := exists_castSucc b hb
      exact hMC (MS_closed (yK E) hyc v₀ b' m hm')
    · rintro a b c d ⟨ha, _⟩ ⟨_, hd, _⟩ _
      exact Or.inl ⟨ha, hd⟩
    · rintro a b c d ⟨ha, _⟩ ⟨_, hd, _⟩ hda
      exact absurd (hda.trans ha) hd
  let N : Submodule ℂ V :=
    { carrier := {m | m ∈ Cl E L M ∧ ∀ a b, ¬ L a b → E a b m ∈ Cl E L M}
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, fun a b h => by
        rw [map_add]; exact add_mem (hx.2 a b h) (hy.2 a b h)⟩
      zero_mem' := ⟨zero_mem _, fun a b _ => by rw [map_zero]; exact zero_mem _⟩
      smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, fun a b h => by
        rw [map_smul]; exact Submodule.smul_mem _ c (hx.2 a b h)⟩ }
  have hv₀N : v₀ ∈ N := by
    refine ⟨hMC hv₀M, ?_⟩
    intro a b hab
    rcases lt_trichotomy a b with h | rfl | h
    · rw [hW.2 a b h]; exact zero_mem _
    · rw [hW.1 a]; exact Submodule.smul_mem _ _ (hMC hv₀M)
    · have ha : a = Fin.last n := by
        by_contra ha
        exact hab ⟨ha, ne_of_lt (lt_of_lt_of_le h (Fin.le_last a)), h⟩
      subst ha
      obtain ⟨b', rfl⟩ := exists_castSucc b (ne_of_lt h)
      exact hMC (MS_closed (yK E) hyc v₀ b' v₀ hv₀M)
  have hNy : ∀ (x : Fin n), ∀ m ∈ N, yK E x m ∈ N := by
    intro x m hm
    obtain ⟨hm1, hm2⟩ : m ∈ Cl E L M ∧ ∀ a b, ¬ L a b → E a b m ∈ Cl E L M := hm
    refine ⟨hY x m hm1, ?_⟩
    intro a b hab
    have hrel := LinearMap.congr_fun (hE a b (Fin.last n) x.castSucc) m
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hrel
    have key : E a b (yK E x m) = E (Fin.last n) x.castSucc (E a b m) +
        ((if b = Fin.last n then E a x.castSucc else 0) m -
          (if x.castSucc = a then E (Fin.last n) b else 0) m) := by
      show E a b (E (Fin.last n) x.castSucc m) = _
      rw [sub_eq_iff_eq_add.mp hrel, add_comm]
    rw [key]
    refine add_mem (hY x _ (hm2 a b hab)) (sub_mem ?_ ?_)
    · split_ifs with hb
      · by_cases hL : L a x.castSucc
        · exact Cl_closed a x.castSucc hL m hm1
        · exact hm2 a x.castSucc hL
      · rw [LinearMap.zero_apply]; exact zero_mem _
    · split_ifs with hxa
      · exact hm2 (Fin.last n) b (hNL b)
      · rw [LinearMap.zero_apply]; exact zero_mem _
  have hMN : M ≤ N := MS_le_of_mem_of_invariant (yK E) v₀ N hv₀N hNy
  have hStab : Stab E (Cl E L M) := by
    intro a b q hq
    by_cases hab : L a b
    · exact Cl_closed a b hab q hq
    · refine gen hE (fun a b => ¬ L a b) L M ?_ (fun a b c d _ _ _ => (em (L a d)).symm)
        (fun a b c d _ _ _ => (em (L c b)).symm) a b hab q hq
      intro a b h m hm'
      have h' : m ∈ Cl E L M ∧ ∀ a b, ¬ L a b → E a b m ∈ Cl E L M := hMN hm'
      exact h'.2 a b h
  have htop : Cl E L M = ⊤ := top_of_stab hI _ hStab v₀ (hMC hv₀M) hv0
  have hker : Cl E L M ≤ LinearMap.ker ξ := by
    apply Cl_le
    · exact MS_le_ker (yK E) v₀ ξ hm
    · intro a b hab q _
      obtain ⟨ha, hb, hba⟩ := hab
      obtain ⟨a', rfl⟩ := exists_castSucc a ha
      obtain ⟨b', rfl⟩ := exists_castSucc b hb
      rw [LinearMap.mem_ker]
      exact hξ a' b' (Fin.castSucc_lt_castSucc_iff.mp hba) q
  ext v
  have hv : v ∈ Cl E L M := by rw [htop]; exact Submodule.mem_top
  rw [LinearMap.zero_apply]
  exact LinearMap.mem_ker.mp (hker hv)

theorem span_singular_vectors : Qr.SpanSing := by
  intro V _ _ _ n E ξ₀ μ w hE hI hξ0 hlow hW hm
  by_contra hw
  obtain ⟨ζ, hζ⟩ := trace_scalar hE hI
  let M : Submodule ℂ V := MS (etaK E) w
  have hec : ∀ a b, etaK E a * etaK E b = etaK E b * etaK E a := etaK_comm hE
  have hwM : w ∈ M := mem_MS (etaK E) w
  have hMη : ∀ (x : Fin n), ∀ q ∈ M, E x.castSucc (Fin.last n) q ∈ M :=
    fun x q hq => MS_closed (etaK E) hec w x q hq
  have hw_up : ∀ a b : Fin (n + 1), a ≤ b → E a b w ∈ M := by
    intro a b hab
    by_cases hb : b = Fin.last n
    · subst hb
      by_cases ha : a = Fin.last n
      · subst ha
        have htr := hζ w
        rw [LinearMap.sum_apply, Fin.sum_univ_castSucc] at htr
        have hdiag : ∀ i : Fin n, E i.castSucc i.castSucc w = μ i • w := fun i => hW.1 i
        have hE' : E (Fin.last n) (Fin.last n) w = ζ • w - ∑ i : Fin n, μ i • w := by
          rw [← htr]
          simp only [hdiag]
          abel
        rw [hE']
        exact sub_mem (Submodule.smul_mem _ _ hwM) (sum_mem fun i _ => Submodule.smul_mem _ _ hwM)
      · obtain ⟨a', rfl⟩ := exists_castSucc a ha
        exact hMη a' w hwM
    · obtain ⟨b', rfl⟩ := exists_castSucc b hb
      have ha : a ≠ Fin.last n := by
        rintro rfl
        exact absurd hab (not_le.mpr (Fin.castSucc_lt_last b'))
      obtain ⟨a', rfl⟩ := exists_castSucc a ha
      rcases (Fin.castSucc_le_castSucc_iff.mp hab).lt_or_eq with h | h
      · rw [show E a'.castSucc b'.castSucc w = subA E a' b' w from rfl, hW.2 a' b' h]
        exact zero_mem _
      · subst h
        rw [show E a'.castSucc a'.castSucc w = subA E a' a' w from rfl, hW.1 a']
        exact Submodule.smul_mem _ _ hwM
  let N : Submodule ℂ V :=
    { carrier := {m | m ∈ M ∧ ∀ a b : Fin (n + 1), a ≤ b → E a b m ∈ M}
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, fun a b h => by
        rw [map_add]; exact add_mem (hx.2 a b h) (hy.2 a b h)⟩
      zero_mem' := ⟨zero_mem _, fun a b _ => by rw [map_zero]; exact zero_mem _⟩
      smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, fun a b h => by
        rw [map_smul]; exact Submodule.smul_mem _ c (hx.2 a b h)⟩ }
  have hNη : ∀ (x : Fin n), ∀ m ∈ N, etaK E x m ∈ N := by
    intro x m hm
    obtain ⟨hm1, hm2⟩ : m ∈ M ∧ ∀ a b : Fin (n + 1), a ≤ b → E a b m ∈ M := hm
    refine ⟨hMη x m hm1, ?_⟩
    intro a b hab
    have hrel := LinearMap.congr_fun (hE a b x.castSucc (Fin.last n)) m
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hrel
    have key : E a b (etaK E x m) = E x.castSucc (Fin.last n) (E a b m) +
        ((if b = x.castSucc then E a (Fin.last n) else 0) m -
          (if Fin.last n = a then E x.castSucc b else 0) m) := by
      show E a b (E x.castSucc (Fin.last n) m) = _
      rw [sub_eq_iff_eq_add.mp hrel, add_comm]
    rw [key]
    refine add_mem (hMη x _ (hm2 a b hab)) (sub_mem ?_ ?_)
    · split_ifs with hb
      · exact hm2 a (Fin.last n) (Fin.le_last a)
      · rw [LinearMap.zero_apply]; exact zero_mem _
    · split_ifs with ha
      · subst ha
        have hb : b = Fin.last n := le_antisymm (Fin.le_last b) hab
        subst hb
        exact hm2 x.castSucc (Fin.last n) (Fin.le_last _)
      · rw [LinearMap.zero_apply]; exact zero_mem _
  have hwN : w ∈ N := ⟨hwM, hw_up⟩
  have hMN : M ≤ N := MS_le_of_mem_of_invariant (etaK E) w N hwN hNη
  let L : Fin (n + 1) → Fin (n + 1) → Prop := fun a b => b < a
  have hStab : Stab E (Cl E L M) := by
    intro a b q hq
    rcases lt_or_ge b a with hab | hab
    · exact Cl_closed a b hab q hq
    · refine gen hE (fun a b => a ≤ b) L M ?_ (fun a b c d _ _ _ => le_or_gt a d)
        (fun a b c d _ _ _ => le_or_gt c b) a b hab q hq
      intro a b h m hm'
      have h' : m ∈ M ∧ ∀ a b : Fin (n + 1), a ≤ b → E a b m ∈ M := hMN hm'
      exact le_Cl E L M (h'.2 a b h)
  have htop := top_of_stab hI _ hStab w (le_Cl E L M hwM) hw
  apply hξ0
  have hker : Cl E L M ≤ LinearMap.ker ξ₀ := by
    apply Cl_le
    · exact MS_le_ker (etaK E) w ξ₀ hm
    · intro a b hab q _
      rw [LinearMap.mem_ker]
      exact hlow a b hab q
  ext v
  have hv : v ∈ Cl E L M := by rw [htop]; exact Submodule.mem_top
  rw [LinearMap.zero_apply]
  exact LinearMap.mem_ker.mp (hker hv)

end Formalism.FourierDecayAlt.P
