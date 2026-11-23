import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.Section

namespace ReciprocityTheory.Coh.InflationTransgression

open ReciprocityTheory.Gal ReciprocityTheory.Coh

universe u

noncomputable section

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_cont_select {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] {Y : Type u} [TopologicalSpace Y] [DiscreteTopology Y] [Nonempty Y]
    (P : X → Y → Prop) (hP : ∀ y, IsOpen {x | P x y}) (hex : ∀ x, ∃ y, P x y) :
    ∃ ψ : X → Y, Continuous ψ ∧ ∀ x, P x (ψ x) := by
  classical
  have hb : TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s} := by
    first
      | exact isTopologicalBasis_isClopen
      | exact isTopologicalBasis_clopen
  choose yx hyx using hex
  have hnb : ∀ x, ∃ C : Set X, IsClopen C ∧ x ∈ C ∧ C ⊆ {x' | P x' (yx x)} := by
    intro x
    obtain ⟨C, hC, hxC, hCs⟩ := hb.exists_subset_of_mem_open (hyx x) (hP (yx x))
    exact ⟨C, hC, hxC, hCs⟩
  choose C hCc hxC hCs using hnb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover C (fun x => (hCc x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxC x⟩)
  have key : ∀ s : Finset X, ∃ ψ : X → Y, Continuous ψ ∧ ∀ x ∈ s, ∀ z ∈ C x, P z (ψ z) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · exact ⟨fun _ => Classical.arbitrary Y, continuous_const, by simp⟩
    · intro a s _ ih
      obtain ⟨ψ, hψc, hψ⟩ := ih
      refine ⟨fun z => if z ∈ C a then yx a else ψ z, ?_, ?_⟩
      · apply continuous_if
        · intro x hx
          have hfr : frontier {x | x ∈ C a} = ∅ := (hCc a).frontier_eq
          rw [hfr] at hx
          simp at hx
        · exact continuous_const.continuousOn
        · exact hψc.continuousOn
      · intro x hx z hz
        by_cases hza : z ∈ C a
        · dsimp only
          rw [if_pos hza]
          exact hCs a hza
        · dsimp only
          rw [if_neg hza]
          rcases Finset.mem_insert.1 hx with rfl | hx'
          · exact absurd hz hza
          · exact hψ x hx' z hz
  obtain ⟨ψ, hψc, hψ⟩ := key t
  refine ⟨ψ, hψc, fun z => ?_⟩
  obtain ⟨x, hx, hz⟩ : ∃ x ∈ t, z ∈ C x := by simpa using ht (Set.mem_univ z)
  exact hψ x hx z hz

def cj (N : Subgroup G) [N.Normal] (s : G) (n : N) : N :=
  ⟨s⁻¹ * n * s, by simpa using (inferInstance : N.Normal).conj_mem n n.2 s⁻¹⟩

@[simp] theorem cj_coe (N : Subgroup G) [N.Normal] (s : G) (n : N) : (cj N s n : G) = s⁻¹ * n * s := rfl

theorem isOpen_setOf_conj_eq (M : TRep R G) [DiscreteTopology M.V] (N : Subgroup G) [N.Normal]
    (hNc : IsClosed (N : Set G)) [CompactSpace G] (f : N → M.V) (hf : Continuous f) (m : M.V) :
    IsOpen {s : G | ∀ n : N, M.rho s (f (cj N s n)) - f n = M.rho n m - m} := by
  have hact : Continuous (fun q : G × M.V => M.rho q.1 q.2) := M.cont
  haveI : CompactSpace N := isCompact_iff_compactSpace.mp hNc.isCompact
  have hcj : Continuous (fun p : G × N => cj N p.1 p.2) := by
    apply Continuous.subtype_mk
    exact (continuous_fst.inv.mul (continuous_subtype_val.comp continuous_snd)).mul continuous_fst
  have hΦ : Continuous (fun p : G × N =>
      M.rho p.1 (f (cj N p.1 p.2)) - f p.2 - (M.rho (p.2 : G) m - m)) := by
    refine ((hact.comp (continuous_fst.prodMk (hf.comp hcj))).sub (hf.comp continuous_snd)).sub ?_
    exact (hact.comp ((continuous_subtype_val.comp continuous_snd).prodMk continuous_const)).sub
      continuous_const
  have hO : IsOpen {p : G × N | M.rho p.1 (f (cj N p.1 p.2)) - f p.2 - (M.rho (p.2 : G) m - m) = 0} :=
    hΦ.isOpen_preimage {0} (isOpen_discrete _)
  rw [isOpen_iff_mem_nhds]
  intro s0 hs0
  have hev : ∀ᶠ s in nhds s0, ∀ n ∈ (Set.univ : Set N),
      M.rho s (f (cj N s n)) - f n - (M.rho (n : G) m - m) = 0 := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro n _
    exact hO.mem_nhds (sub_eq_zero.mpr (hs0 n))
  filter_upwards [hev] with s hs n
  exact sub_eq_zero.mp (hs n (Set.mem_univ n))

theorem exists_ext_cochain [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : TRep R G) [DiscreteTopology M.V] (N : Subgroup G) [N.Normal] (hNc : IsClosed (N : Set G))
    (f : N → M.V) (hf : Continuous f) (hfc : ∀ a b : N, f (a * b) = f a + M.rho a (f b))
    (hinv : ∀ s : G, ∃ m : M.V, ∀ n : N, M.rho s (f (cj N s n)) - f n = M.rho n m - m) :
    ∃ y : G → M.V, Continuous y ∧ (∀ n : N, y n = f n) ∧
      (∀ g (n : N), y (g * n) = y g + M.rho g (f n)) ∧
      (∀ (n : N) g, y (n * g) = f n + M.rho n (y g)) := by
  have : Nonempty M.V := ⟨0⟩
  obtain ⟨ψ, hψc, hψ⟩ := exists_cont_select
    (fun s m => ∀ n : N, M.rho s (f (cj N s n)) - f n = M.rho n m - m)
    (isOpen_setOf_conj_eq M N hNc f hf) hinv
  obtain ⟨r, hrc, hr1, hr⟩ := groupSection_holds G N hNc
  have hf1 : f 1 = 0 := by
    have e := hfc 1 1
    simp only [mul_one, OneMemClass.coe_one, map_one, Module.End.one_apply] at e
    exact (left_eq_add.1 e)
  have hψ1 : ∀ n : N, M.rho n (ψ 1) = ψ 1 := fun n => by
    have e := hψ 1 n
    have hc : cj N 1 n = n := Subtype.ext (by simp)
    rw [hc, map_one, Module.End.one_apply, sub_self] at e
    exact (sub_eq_zero.1 e.symm)
  have hrσ : ∀ g, r ((r g : G)⁻¹ * g) = 1 := fun g => by
    have e := hr (r g)⁻¹ g
    rw [InvMemClass.coe_inv] at e
    rw [e, inv_mul_cancel]
  set σ : G → G := fun g => (r g : G)⁻¹ * g with hσ
  set y : G → M.V := fun g => f (r g) + M.rho (r g) (ψ (σ g)) - ψ 1 with hy
  have hσn : ∀ (n : N) g, σ (n * g) = σ g := fun n g => by
    simp only [hσ, hr n g, Subgroup.coe_mul, mul_inv_rev]; group
  have h3 : ∀ (n : N) g, y (n * g) = f n + M.rho n (y g) := fun n g => by
    simp only [hy, hσn, hr n g, hfc, Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_add,
      map_sub, hψ1]
    abel
  have h2 : ∀ g (n : N), y (g * n) = y g + M.rho g (f n) := fun g n => by
    set t := σ g with ht
    let n'' : N := ⟨t * n * t⁻¹, (inferInstance : N.Normal).conj_mem n n.2 t⟩
    have hg : (r g : G) * t = g := by simp [ht, hσ]
    have e1 : g * n = ((r g * n'' : N) : G) * t := by
      simp only [Subgroup.coe_mul, n'']
      calc g * n = (r g : G) * t * n := by rw [hg]
        _ = _ := by group
    have hrgn : r (g * n) = r g * n'' := by rw [e1, hr, hrσ g, mul_one]
    have hσgn : σ (g * n) = t := by
      show ((r (g * n) : G))⁻¹ * (g * n) = t
      rw [hrgn, e1]; group
    have hc : cj N t n'' = n := Subtype.ext (by simp [n'']; group)
    have e2 := hψ t n''
    rw [hc] at e2
    have e3 : f n'' + M.rho n'' (ψ t) = M.rho t (f n) + ψ t := by
      rw [sub_eq_sub_iff_add_eq_add] at e2
      rw [add_comm (f n''), ← e2]
    have hrg : M.rho g = M.rho (r g) * M.rho t := by rw [← map_mul, hg]
    show f (r (g * n)) + M.rho (r (g * n)) (ψ (σ (g * n))) - ψ 1 = y g + M.rho g (f n)
    rw [hrgn, hσgn, hfc]
    calc _ = f (r g) + M.rho (r g) (f n'' + M.rho n'' (ψ t)) - ψ 1 := by
          rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_add]; abel
      _ = f (r g) + M.rho (r g) (M.rho t (f n) + ψ t) - ψ 1 := by rw [e3]
      _ = _ := by rw [map_add, hrg, Module.End.mul_apply, hy]; simp only [← ht]; abel
  have hy1 : y 1 = 0 := by simp [hy, hr1, hf1, hσ]
  refine ⟨y, ?_, fun n => by simpa [hy1] using h3 n 1, h2, h3⟩
  have hr' : Continuous fun g => (r g : G) := continuous_subtype_val.comp hrc
  exact ((hf.comp hrc).add (M.cont.comp (hr'.prodMk (hψc.comp (hr'.inv.mul continuous_id))))).sub
    continuous_const

def D1 (M : TRep R G) (y : G → M.V) (a b : G) : M.V := M.rho a (y b) - y (a * b) + y a

structure InflD (M : TRep R G) (N : Subgroup G) (D : G → G → M.V) : Prop where
  right : ∀ a b (n : N), D a (b * n) = D a b
  left : ∀ a b (n : N), D (a * n) b = D a b
  inv : ∀ a b (n : N), M.rho n (D a b) = D a b

theorem inflD_of_ext (M : TRep R G) (N : Subgroup G) [N.Normal] (f : N → M.V) (y : G → M.V)
    (h2 : ∀ g (n : N), y (g * n) = y g + M.rho g (f n))
    (h3 : ∀ (n : N) g, y (n * g) = f n + M.rho n (y g)) : InflD M N (D1 M y) := by
  have hc : ∀ (c : G) (n : N), M.rho n (y c) = y c + M.rho c (f (cj N c n)) - f n := by
    intro c n
    have e : (n : G) * c = c * (cj N c n : G) := by rw [cj_coe]; group
    have h := h3 n c
    rw [e, h2] at h
    exact sub_eq_zero.mp (Eq.trans (by abel) (sub_eq_zero.mpr h.symm))
  refine ⟨?_, ?_, ?_⟩
  · intro a b n
    simp only [D1]
    rw [h2 b n, ← mul_assoc, h2 (a * b) n]
    simp only [map_add, map_sub, map_mul, Module.End.mul_apply]
    abel
  · intro a b n
    simp only [D1]
    have e : a * (n : G) * b = a * b * (cj N b n : G) := by rw [cj_coe]; group
    rw [e, h2 (a * b), h2 a n]
    simp only [map_mul, Module.End.mul_apply]
    rw [hc b n]
    simp only [map_add, map_sub, map_mul, Module.End.mul_apply]
    abel
  · intro a b n
    simp only [D1, map_add, map_sub]
    rw [hc (a * b) n, hc a n]
    have e : (n : G) * a = a * (cj N a n : G) := by rw [cj_coe]; group
    have e2 : M.rho n (M.rho a (y b)) = M.rho a (M.rho (cj N a n) (y b)) := by
      rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
    have e3 : cj N b (cj N a n) = cj N (a * b) n := by
      apply Subtype.ext
      simp only [cj_coe]
      group
    rw [e2, hc b (cj N a n), e3]
    simp only [map_add, map_sub, map_mul, Module.End.mul_apply]
    abel

section
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (y : G → M.V) (hy1 : y 1 = 0)
  (hD : InflD M N (D1 M y))
include hy1 hD

theorem inflD_mul_right (a : G) (n : N) : y (a * n) = y a + M.rho a (y n) := by
  have h := hD.right a 1 n
  simp only [D1, one_mul, mul_one, hy1, map_zero] at h
  exact sub_eq_zero.mp (Eq.trans (by abel) (sub_eq_zero.mpr h.symm))

theorem inflD_mul_left (n : N) (a : G) : y (n * a) = y n + M.rho n (y a) := by
  have h := hD.left 1 a n
  simp only [D1, one_mul, hy1, map_one, Module.End.one_apply] at h
  exact sub_eq_zero.mp (Eq.trans (by abel) (sub_eq_zero.mpr h.symm))

theorem inflD_conj (s : G) (n : N) : M.rho s (y (cj N s n)) - y n = M.rho n (y s) - y s := by
  have h1 := inflD_mul_right M N y hy1 hD s (cj N s n)
  have h2 := inflD_mul_left M N y hy1 hD n s
  have he : s * (cj N s n : G) = (n : G) * s := by rw [cj_coe]; group
  rw [he, h2] at h1
  exact sub_eq_zero.mp (Eq.trans (by abel) (sub_eq_zero.mpr h1.symm))

theorem inflD_of_zero (hz : ∀ n : N, y n = 0) :
    (∀ a (n : N), y (a * n) = y a) ∧ ∀ a (n : N), M.rho n (y a) = y a := by
  refine ⟨fun a n => ?_, fun a n => ?_⟩
  · rw [inflD_mul_right M N y hy1 hD a n, hz, map_zero, add_zero]
  · have h := inflD_conj M N y hy1 hD a n
    simp only [hz, map_zero, sub_zero] at h
    exact sub_eq_zero.mp h.symm

end

end

end ReciprocityTheory.Coh.InflationTransgression
