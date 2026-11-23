import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.ColFilt

section Abstract

variable {A B : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]

def ConeAcyclic (dA : ∀ n m, A n →+ A m) (dB : ∀ n m, B n →+ B m) (Φ : ∀ n, A n →+ B n) : Prop :=
  ∀ n₀ n₁ n₂ n₃ : ℤ, n₀ + 1 = n₁ → n₁ + 1 = n₂ → n₂ + 1 = n₃ → ∀ (x : A n₂) (y : B n₁),
    dA n₂ n₃ x = 0 → Φ n₂ x = dB n₁ n₂ y → ∃ (v : A n₁) (w : B n₀), x = dA n₁ n₂ v ∧ y = Φ n₁ v + dB n₀ n₁ w

structure IsFilt {G : ℤ → ℤ → Type*} [∀ p n, AddCommGroup (G p n)] (d : ∀ n m, A n →+ A m)
    (g : ∀ p n m, G p n →+ G p m) (F : ℤ → ∀ n, AddSubgroup (A n)) (r : ∀ p n m, n + p = m → (A n →+ G p m)) : Prop where
  dd : ∀ n m k x, d m k (d n m x) = 0
  dF : ∀ p n m, n + 1 = m → ∀ x ∈ F p n, d n m x ∈ F p m
  rd : ∀ p n m n' m' (hn : n + p = n') (hm : m + p = m'), n + 1 = m → ∀ x ∈ F p n,
    r p m m' hm (d n m x) = g p n' m' (r p n n' hn x)
  mono : ∀ p q n, p ≤ q → F p n ≤ F q n
  ker : ∀ p n m (h : n + p = m), ∀ x ∈ F p n, r p n m h x = 0 ↔ x ∈ F (p - 1) n
  surj : ∀ p n m (h : n + p = m) (y : G p m), ∃ x ∈ F p n, r p n m h x = y
  top : ∀ n x, x ∈ F 0 n
  bot : ∀ n, ∃ N, ∀ x ∈ F N n, x = 0

variable {GA GB : ℤ → ℤ → Type*} [∀ p n, AddCommGroup (GA p n)] [∀ p n, AddCommGroup (GB p n)]
  {dA : ∀ n m, A n →+ A m} {gA : ∀ p n m, GA p n →+ GA p m} {FA : ℤ → ∀ n, AddSubgroup (A n)}
  {rA : ∀ p n m, n + p = m → (A n →+ GA p m)}
  {dB : ∀ n m, B n →+ B m} {gB : ∀ p n m, GB p n →+ GB p m} {FB : ℤ → ∀ n, AddSubgroup (B n)}
  {rB : ∀ p n m, n + p = m → (B n →+ GB p m)}

theorem exists_graded (hA : IsFilt dA gA FA rA) (hB : IsFilt dB gB FB rB) (Φ : ∀ n, A n →+ B n)
    (hd : ∀ n m, n + 1 = m → ∀ x, Φ m (dA n m x) = dB n m (Φ n x))
    (hF : ∀ p n, ∀ x ∈ FA p n, Φ n x ∈ FB p n) (p : ℤ) :
    ∃ Ψ : ∀ m, GA p m →+ GB p m,
      (∀ n m (h : n + p = m), ∀ x ∈ FA p n, Ψ m (rA p n m h x) = rB p n m h (Φ n x)) ∧
      ∀ n m, n + 1 = m → ∀ y, Ψ m (gA p n m y) = gB p n m (Ψ n y) := by
  have key : ∀ n m (h : n + p = m), ∀ x ∈ FA p n, ∀ x' ∈ FA p n, rA p n m h x = rA p n m h x' →
      rB p n m h (Φ n x) = rB p n m h (Φ n x') := by
    intro n m h x hx x' hx' e
    have h1 : x - x' ∈ FA p n := sub_mem hx hx'
    have h2 := (hA.ker p n m h _ h1).1 (by rw [map_sub, e, sub_self])
    have h3 := (hB.ker p n m h _ (hF _ _ _ h1)).2 (hF _ _ _ h2)
    rwa [map_sub, map_sub, sub_eq_zero] at h3
  choose s hs hs' using fun m => hA.surj p (m - p) m (by omega)
  let Ψ : ∀ m, GA p m →+ GB p m := fun m => AddMonoidHom.mk' (fun y => rB p (m - p) m (by omega) (Φ _ (s m y)))
    (fun y y' => by
      rw [← map_add, ← map_add]
      exact key _ _ _ _ (hs _ _) _ (add_mem (hs _ _) (hs _ _)) (by rw [map_add, hs', hs', hs']))
  have h1 : ∀ n m (h : n + p = m), ∀ x ∈ FA p n, Ψ m (rA p n m h x) = rB p n m h (Φ n x) := by
    intro n m h x hx
    obtain rfl : n = m - p := by omega
    exact key _ _ _ _ (hs _ _) _ hx (hs' _ _)
  refine ⟨Ψ, h1, fun n m hnm y => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hA.surj p (n - p) n (by omega) y
  rw [← hA.rd p (n - p) (m - p) n m _ (by omega) (by omega) x hx, h1 _ _ _ _ (hA.dF _ _ _ (by omega) _ hx),
    hd _ _ (by omega), hB.rd p (n - p) (m - p) n m (by omega) _ (by omega) _ (hF _ _ _ hx), h1 _ _ _ _ hx]

theorem coneAcyclic_of_graded (hA : IsFilt dA gA FA rA) (hB : IsFilt dB gB FB rB) (Φ : ∀ n, A n →+ B n)
    (hd : ∀ n m, n + 1 = m → ∀ x, Φ m (dA n m x) = dB n m (Φ n x))
    (hF : ∀ p n, ∀ x ∈ FA p n, Φ n x ∈ FB p n) (Ψ : ∀ p m, GA p m →+ GB p m)
    (hΨ : ∀ p n m (h : n + p = m), ∀ x ∈ FA p n, Ψ p m (rA p n m h x) = rB p n m h (Φ n x))
    (hc : ∀ p ≤ 0, ConeAcyclic (gA p) (gB p) (Ψ p)) : ConeAcyclic dA dB Φ := by
  intro n₀ n₁ n₂ n₃ h₀ h₁ h₂
  obtain ⟨N, hN⟩ := hA.bot n₂
  obtain ⟨N', hN'⟩ := hB.bot n₁
  have main : ∀ p, min (min N N') 0 ≤ p → p ≤ 0 → ∀ x ∈ FA p n₂, ∀ y ∈ FB p n₁,
      dA n₂ n₃ x = 0 → Φ n₂ x = dB n₁ n₂ y → ∃ (v : A n₁) (w : B n₀), x = dA n₁ n₂ v ∧ y = Φ n₁ v + dB n₀ n₁ w := by
    intro p hp
    induction p, hp using Int.le_induction with
    | base =>
      intro _ x hx y hy _ _
      refine ⟨0, 0, ?_, ?_⟩
      · simpa using hN x (hA.mono _ _ _ (by omega) hx)
      · simpa using hN' y (hB.mono _ _ _ (by omega) hy)
    | succ p _ ih =>
      intro hp0 x hx y hy hdx hxy
      obtain ⟨v', w', hv, hw⟩ := hc (p + 1) hp0 (n₀ + (p + 1)) (n₁ + (p + 1)) (n₂ + (p + 1)) (n₃ + (p + 1))
        (by omega) (by omega) (by omega) (rA _ _ _ rfl x) (rB _ _ _ rfl y)
        (by rw [← hA.rd _ _ n₃ _ _ rfl rfl h₂ x hx, hdx, map_zero])
        (by rw [hΨ _ _ _ _ _ hx, hxy, hB.rd _ _ _ _ _ rfl rfl h₁ y hy])
      obtain ⟨v, hvF, rfl⟩ := hA.surj _ n₁ _ rfl v'
      obtain ⟨w, hwF, rfl⟩ := hB.surj _ n₀ _ rfl w'
      have hx' : x - dA n₁ n₂ v ∈ FA p n₂ := by
        have := (hA.ker _ _ _ rfl _ (sub_mem hx (hA.dF _ _ _ h₁ _ hvF))).1
          (by rw [map_sub, hA.rd _ _ _ _ _ rfl rfl h₁ v hvF, ← hv, sub_self])
        rwa [add_sub_cancel_right] at this
      have hy' : y - (Φ n₁ v + dB n₀ n₁ w) ∈ FB p n₁ := by
        have := (hB.ker _ _ _ rfl _ (sub_mem hy (add_mem (hF _ _ _ hvF) (hB.dF _ _ _ h₀ _ hwF)))).1
          (by rw [map_sub, map_add, hB.rd _ _ _ _ _ rfl rfl h₀ w hwF, ← hΨ _ _ _ _ _ hvF, ← hw, sub_self])
        rwa [add_sub_cancel_right] at this
      obtain ⟨v₂, w₂, e₁, e₂⟩ := ih (by omega) _ hx' _ hy'
        (by rw [map_sub, hdx, hA.dd, sub_self])
        (by rw [map_sub, map_sub, map_add, hB.dd, add_zero, hxy, hd _ _ h₁])
      refine ⟨v + v₂, w + w₂, ?_, ?_⟩
      · rw [map_add, ← e₁]; abel
      · rw [map_add, map_add, add_add_add_comm, ← e₂]; abel
  intro x y
  exact main 0 (min_le_right _ _) le_rfl x (hA.top _ _) y (hB.top _ _)

end Abstract

section Classes
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

def dC (K I : CochainComplex C ℤ) (n m : ℤ) : Cochain K I n →+ Cochain K I m :=
  AddMonoidHom.mk' (δ n m) (δ_add n m)

def dPi {J : Type*} (K : CochainComplex C ℤ) (I : J → CochainComplex C ℤ) (e : J → ℤ) (n m : ℤ) :
    (∀ j, Cochain K (I j) (n - e j)) →+ ∀ j, Cochain K (I j) (m - e j) :=
  AddMonoidHom.mk' (fun α j => δ _ _ (α j)) (fun _ _ => funext fun _ => δ_add _ _ _ _)

variable {J : Type*} {K K' I' : CochainComplex C ℤ} {I : J → CochainComplex C ℤ} {e : J → ℤ}
  (Φ : ∀ n, (∀ j, Cochain K (I j) (n - e j)) →+ Cochain K' I' n)

theorem mk_eq_mk_iff {n : ℤ} (a b : Cocycle K' I' n) (m : ℤ) (h : m + 1 = n) :
    CohomologyClass.mk a = CohomologyClass.mk b ↔ ∃ w : Cochain K' I' m, δ m n w = a.1 - b.1 := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m h]
  rfl

theorem bijective_of_coneAcyclic
    (hd : ∀ n m, n + 1 = m → ∀ α, Φ m (fun j => δ _ _ (α j)) = δ n m (Φ n α))
    (hc : ConeAcyclic (dPi K I e) (dC K' I') Φ) (n : ℤ)
    (φ : (∀ j, CohomologyClass K (I j) (n - e j)) → CohomologyClass K' I' n)
    (hφ : ∀ (a : ∀ j, Cocycle K (I j) (n - e j)) (b : Cocycle K' I' n), b.1 = Φ n (fun j => (a j).1) →
      φ (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b) : Function.Bijective φ := by
  have hz : ∀ a : ∀ j, Cocycle K (I j) (n - e j), δ n (n + 1) (Φ n (fun j => (a j).1)) = 0 := by
    intro a
    rw [← hd _ _ rfl, ← map_zero (Φ (n + 1))]
    congr 1
    funext j
    exact Cocycle.δ_eq_zero (a j) _
  constructor
  · intro x x' h
    choose a ha using fun j => CohomologyClass.mk_surjective (x j)
    choose a' ha' using fun j => CohomologyClass.mk_surjective (x' j)
    obtain rfl : (fun j => CohomologyClass.mk (a j)) = x := funext ha
    obtain rfl : (fun j => CohomologyClass.mk (a' j)) = x' := funext ha'
    rw [hφ a (Cocycle.mk _ _ rfl (hz a)) rfl, hφ a' (Cocycle.mk _ _ rfl (hz a')) rfl,
      mk_eq_mk_iff _ _ (n - 1) (by omega)] at h
    obtain ⟨w, hw⟩ := h
    obtain ⟨v, -, hv, -⟩ := hc (n - 2) (n - 1) n (n + 1) (by omega) (by omega) rfl
      ((fun j => (a j).1) - fun j => (a' j).1) w
      (funext fun j => Cocycle.δ_eq_zero (a j - a' j) _) (by rw [map_sub]; exact hw.symm)
    funext j
    rw [mk_eq_mk_iff _ _ (n - 1 - e j) (by omega)]
    exact ⟨v j, (congrFun hv j).symm⟩
  · intro y
    obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective y
    obtain ⟨v, w, hv, hw⟩ := hc (n - 1) n (n + 1) (n + 2) (by omega) rfl (by omega) 0 b.1 (map_zero _)
      (by rw [map_zero]; exact (Cocycle.δ_eq_zero b _).symm)
    let a : ∀ j, Cocycle K (I j) (n - e j) := fun j => Cocycle.mk (v j) (n + 1 - e j) (by omega) (congrFun hv j).symm
    refine ⟨fun j => CohomologyClass.mk (a j), ?_⟩
    rw [hφ a (Cocycle.mk _ _ rfl (hz a)) rfl, eq_comm, mk_eq_mk_iff _ _ (n - 1) (by omega)]
    refine ⟨w, ?_⟩
    rw [eq_sub_iff_add_eq', hw]
    rfl

theorem coneAcyclic_of_bijective
    (hd : ∀ n m, n + 1 = m → ∀ α, Φ m (fun j => δ _ _ (α j)) = δ n m (Φ n α))
    (φ : ∀ n, (∀ j, CohomologyClass K (I j) (n - e j)) → CohomologyClass K' I' n)
    (hφ : ∀ n (a : ∀ j, Cocycle K (I j) (n - e j)) (b : Cocycle K' I' n), b.1 = Φ n (fun j => (a j).1) →
      φ n (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b)
    (hb : ∀ n, Function.Bijective (φ n)) : ConeAcyclic (dPi K I e) (dC K' I') Φ := by
  intro n₀ n₁ n₂ n₃ h₀ h₁ h₂ x y hx hxy
  have hxy' : Φ n₂ x = δ n₁ n₂ y := hxy
  let a : ∀ j, Cocycle K (I j) (n₂ - e j) := fun j => Cocycle.mk (x j) (n₃ - e j) (by omega) (congrFun hx j)
  have h1 : (fun j => CohomologyClass.mk (a j)) = fun j => CohomologyClass.mk (0 : Cocycle K (I j) (n₂ - e j)) := by
    apply (hb n₂).1
    rw [hφ n₂ a (Cocycle.mk (δ n₁ n₂ y) n₃ h₂ (δ_δ _ _ _ _)) hxy'.symm,
      hφ n₂ (fun _ => 0) 0 (map_zero (Φ n₂)).symm, mk_eq_mk_iff _ _ n₁ h₁]
    exact ⟨y, (sub_zero _).symm⟩
  choose v hv using fun j => (mk_eq_mk_iff _ _ (n₁ - e j) (by omega)).1 (congrFun h1 j)
  have hv' : (fun j => δ _ _ (v j)) = x := funext fun j => (hv j).trans (sub_zero _)
  let b : Cocycle K' I' n₁ := Cocycle.mk (y - Φ n₁ v) n₂ h₁ (by rw [δ_sub, ← hd _ _ h₁, hv', hxy', sub_self])
  obtain ⟨c, hc⟩ := (hb n₁).2 (CohomologyClass.mk b)
  choose a' ha' using fun j => CohomologyClass.mk_surjective (c j)
  obtain rfl : (fun j => CohomologyClass.mk (a' j)) = c := funext ha'
  have h0 : (fun j => δ (n₁ - e j) (n₂ - e j) (a' j).1) = 0 := funext fun j => Cocycle.δ_eq_zero (a' j) _
  rw [hφ n₁ a' (Cocycle.mk _ n₂ h₁ (by rw [← hd _ _ h₁, h0, map_zero])) rfl, eq_comm,
    mk_eq_mk_iff _ _ n₀ h₀] at hc
  obtain ⟨w, hw⟩ := hc
  refine ⟨v + fun j => (a' j).1, w, ?_, ?_⟩
  · rw [map_add]
    exact (by rw [← hv']; exact ((congrArg₂ (· + ·) rfl h0).trans (add_zero _)).symm)
  · have hw' : δ n₀ n₁ w = y - Φ n₁ v - Φ n₁ fun j => (a' j).1 := hw
    change y = _ + δ n₀ n₁ w
    rw [hw', map_add]; abel

end Classes

section Columns
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

structure IsColumns (K : CochainComplex C ℤ) (Col : ℤ → CochainComplex C ℤ)
    (ι : ∀ p k t, p + k = t → ((Col p).X k ⟶ K.X t)) : Prop where
  ext : ∀ (t : ℤ) {Y : C} (f : K.X t ⟶ Y), (∀ p k h, ι p k t h ≫ f = 0) → f = 0
  desc : ∀ (p k t : ℤ) (h : p + k = t) {Y : C} (g : (Col p).X k ⟶ Y),
    ∃ f : K.X t ⟶ Y, ι p k t h ≫ f = g ∧ ∀ c l h', c ≠ p → ι c l t h' ≫ f = 0
  diff : ∀ (p k t k' t' : ℤ) (h : p + k = t) (h' : p + k' = t'), k + 1 = k' → ∀ {Y : C} (f : K.X t' ⟶ Y),
    (∀ c l h'', p < c → ι c l t' h'' ≫ f = 0) →
      ι p k t h ≫ K.d t t' ≫ f = p.negOnePow • (Col p).d k k' ≫ ι p k' t' h' ≫ f
  isZero : ∀ p k, 0 < p ∨ 0 < k → IsZero ((Col p).X k)

variable {K : CochainComplex C ℤ} {Col : ℤ → CochainComplex C ℤ} (ι : ∀ p k t, p + k = t → ((Col p).X k ⟶ K.X t))
  (I : CochainComplex C ℤ)

def van (p n : ℤ) : AddSubgroup (Cochain K I n) where
  carrier := {α | ∀ c k t h q hq, p < c → ι c k t h ≫ α.v t q hq = 0}
  zero_mem' := by intro c k t h q hq _; simp
  add_mem' := by intro α β hα hβ c k t h q hq hc; simp [hα c k t h q hq hc, hβ c k t h q hq hc]
  neg_mem' := by intro α hα c k t h q hq hc; simp [hα c k t h q hq hc]

def restr (p n m : ℤ) (h : n + p = m) : Cochain K I n →+ Cochain (Col p) I m :=
  AddMonoidHom.mk' (fun α => Cochain.mk fun k q hq => ι p k (p + k) rfl ≫ α.v (p + k) q (by omega))
    (fun α β => by ext k q hq; simp)

theorem restr_v (p n m : ℤ) (h : n + p = m) (α : Cochain K I n) (k t q : ℤ) (ht : p + k = t) (hq : k + m = q)
    (hq' : t + n = q) : (restr ι I p n m h α).v k q hq = ι p k t ht ≫ α.v t q hq' := by
  subst ht; rfl

variable {ι}

theorem IsColumns.ι_δ (hK : IsColumns K Col ι) {p n m n' m' : ℤ} (hn : n + p = n') (hm : m + p = m') (h : n + 1 = m)
    {α : Cochain K I n} {p₀ : ℤ} (hp : p₀ ≤ p) (hα : α ∈ van ι I p₀ n) :
    restr ι I p m m' hm (δ n m α) = δ n' m' (restr ι I p n n' hn α) := by
  ext k q hq
  rw [restr_v ι I p m m' hm _ k (p + k) q rfl hq (by omega),
    δ_v n m h α (p + k) q _ (q - 1) (p + k + 1) rfl rfl,
    δ_v n' m' (by omega) _ k q hq (q - 1) (k + 1) rfl rfl,
    restr_v ι I p n n' hn _ k (p + k) (q - 1) rfl _ (by omega),
    restr_v ι I p n n' hn _ (k + 1) (p + k + 1) q (by omega) _ (by omega),
    Preadditive.comp_add, Linear.comp_units_smul,
    hK.diff p k (p + k) (k + 1) (p + k + 1) rfl (by omega) rfl _ (fun c l h'' hc => hα c l _ h'' _ _ (by omega)),
    smul_smul, ← Int.negOnePow_add, hm, Category.assoc]

theorem mem_van_iff {p n : ℤ} (α : Cochain K I n) :
    α ∈ van ι I p n ↔ ∀ c, p < c → restr ι I c n (n + c) rfl α = 0 := by
  constructor
  · intro hα c hc
    ext k q hq
    exact hα c k _ _ _ _ hc
  · intro hα c k t h q hq hc
    rw [← restr_v ι I c n (n + c) rfl α k t q h (by omega) hq, hα c hc, Cochain.zero_v]

theorem IsColumns.isFilt (hK : IsColumns K Col ι) [I.IsStrictlyGE 0] :
    IsFilt (dC K I) (fun p => dC (Col p) I) (van ι I) (restr ι I) where
  dd n m k x := δ_δ _ _ _ _
  dF p n m h α hα := by
    rw [mem_van_iff]
    intro c hc
    change restr ι I c m (m + c) rfl (δ n m α) = 0
    rw [hK.ι_δ I rfl rfl h hc.le hα, (mem_van_iff I α).1 hα c hc, δ_zero]
  rd p n m n' m' hn hm h α hα := hK.ι_δ I hn hm h le_rfl hα
  mono p q n hpq α hα c k t h s hs hc := hα c k t h s hs (by omega)
  ker p n m h α hα := by
    subst h
    rw [mem_van_iff] at hα ⊢
    refine ⟨fun h0 c hc => ?_, fun h0 => h0 p (by omega)⟩
    by_cases hcp : c = p
    · subst hcp; exact h0
    · exact hα c (by omega)
  surj p n m h y := by
    choose f hf hf' using fun t q (hq : t + n = q) => hK.desc p (t - p) t (by omega) (y.v (t - p) q (by omega))
    refine ⟨Cochain.mk f, fun c k t ht q hq hc => hf' t q hq c k ht (by omega), ?_⟩
    ext k q hq
    obtain ⟨t, rfl⟩ : ∃ t, k = t - p := ⟨k + p, by omega⟩
    rw [restr_v ι I p n m h _ (t - p) t q (by omega) hq (by omega)]
    exact hf t q _
  top n α c k t h q hq hc := (hK.isZero c k (Or.inl hc)).eq_of_src _ _
  bot n := by
    refine ⟨-n - 1, fun α hα => ?_⟩
    ext t q hq
    refine hK.ext t _ fun p k h => ?_
    by_cases hp : -n - 1 < p
    · exact hα p k t h q hq hp
    · by_cases hk : 0 < k
      · exact (hK.isZero p k (Or.inr hk)).eq_of_src _ _
      · exact (I.isZero_of_isStrictlyGE 0 q (by omega)).eq_of_tgt _ _

variable (ι) {J : Type*} (Ij : J → CochainComplex C ℤ) (e : J → ℤ)

def vanPi (p n : ℤ) : AddSubgroup (∀ j, Cochain K (Ij j) (n - e j)) :=
  AddSubgroup.pi Set.univ fun j => van ι (Ij j) p (n - e j)

def restrPi (p n m : ℤ) (h : n + p = m) :
    (∀ j, Cochain K (Ij j) (n - e j)) →+ ∀ j, Cochain (Col p) (Ij j) (m - e j) :=
  AddMonoidHom.mk' (fun α j => restr ι (Ij j) p (n - e j) (m - e j) (by omega) (α j))
    (fun _ _ => funext fun _ => map_add _ _ _)

variable {ι}

theorem IsColumns.isFilt_pi (hK : IsColumns K Col ι) [Finite J] [∀ j, (Ij j).IsStrictlyGE 0] :
    IsFilt (dPi K Ij e) (fun p => dPi (Col p) Ij e) (vanPi ι Ij e) (restrPi ι Ij e) where
  dd n m k x := funext fun _ => δ_δ _ _ _ _
  dF p n m h α hα j hj := (hK.isFilt (Ij j)).dF p _ _ (by omega) _ (hα j hj)
  rd p n m n' m' hn hm h α hα := funext fun j =>
    (hK.isFilt (Ij j)).rd p _ _ _ _ (by omega) (by omega) (by omega) _ (hα j trivial)
  mono p q n hpq α hα j hj := (hK.isFilt (Ij j)).mono p q _ hpq (hα j hj)
  ker p n m h α hα :=
    ⟨fun h0 j hj => ((hK.isFilt (Ij j)).ker p _ (m - e j) (by omega) _ (hα j hj)).1 (congrFun h0 j),
      fun h0 => funext fun j => ((hK.isFilt (Ij j)).ker p _ (m - e j) (by omega) _ (hα j trivial)).2 (h0 j trivial)⟩
  surj p n m h y := by
    choose x hx hx' using fun j => (hK.isFilt (Ij j)).surj p (n - e j) (m - e j) (by omega) (y j)
    exact ⟨x, fun j _ => hx j, funext hx'⟩
  top n α j _ := (hK.isFilt (Ij j)).top _ _
  bot n := by
    choose N hN using fun j => (hK.isFilt (Ij j)).bot (n - e j)
    obtain ⟨M, hM⟩ := (Set.finite_range N).bddBelow
    exact ⟨M, fun α hα => funext fun j =>
      hN j _ ((hK.isFilt (Ij j)).mono _ _ _ (hM ⟨j, rfl⟩) (hα j trivial))⟩

theorem bijective_of_columns {L T : CochainComplex C ℤ} {CL CT : ℤ → CochainComplex C ℤ}
    {ιL : ∀ p k t, p + k = t → ((CL p).X k ⟶ L.X t)} {ιT : ∀ p k t, p + k = t → ((CT p).X k ⟶ T.X t)}
    (hL : IsColumns L CL ιL) (hT : IsColumns T CT ιT) {J : Type*} [Finite J] (Ij : J → CochainComplex C ℤ)
    [∀ j, (Ij j).IsStrictlyGE 0] (I : CochainComplex C ℤ) [I.IsStrictlyGE 0] (e : J → ℤ)
    (Φ : ∀ n, (∀ j, Cochain L (Ij j) (n - e j)) →+ Cochain T I n)
    (hd : ∀ n m, n + 1 = m → ∀ α, Φ m (fun j => δ _ _ (α j)) = δ n m (Φ n α))
    (hF : ∀ p n α, (∀ j, α j ∈ van ιL (Ij j) p (n - e j)) → Φ n α ∈ van ιT I p n)
    (hG : ∀ p ≤ 0, ∃ ψ : ∀ m, (∀ j, CohomologyClass (CL p) (Ij j) (m - e j)) → CohomologyClass (CT p) I m,
      (∀ m, Function.Bijective (ψ m)) ∧
      ∀ n m (h : n + p = m) (α : ∀ j, Cochain L (Ij j) (n - e j)), (∀ j, α j ∈ van ιL (Ij j) p (n - e j)) →
        ∀ (a : ∀ j, Cocycle (CL p) (Ij j) (m - e j)) (b : Cocycle (CT p) I m),
          (∀ j, (a j).1 = restr ιL (Ij j) p (n - e j) (m - e j) (by omega) (α j)) →
          b.1 = restr ιT I p n m h (Φ n α) → ψ m (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b)
    (n : ℤ) (φ : (∀ j, CohomologyClass L (Ij j) (n - e j)) → CohomologyClass T I n)
    (hφ : ∀ (a : ∀ j, Cocycle L (Ij j) (n - e j)) (b : Cocycle T I n), b.1 = Φ n (fun j => (a j).1) →
      φ (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b) : Function.Bijective φ := by
  have hA := hL.isFilt_pi Ij e
  have hB := hT.isFilt I
  have hF' : ∀ p n, ∀ α ∈ vanPi ιL Ij e p n, Φ n α ∈ van ιT I p n := fun p n α hα => hF p n α fun j => hα j trivial
  choose Ψ hΨ hΨd using exists_graded hA hB Φ hd hF'
  refine bijective_of_coneAcyclic Φ hd (coneAcyclic_of_graded hA hB Φ hd hF' Ψ hΨ fun p hp => ?_) n φ hφ
  obtain ⟨ψ, hb, hψ⟩ := hG p hp
  refine coneAcyclic_of_bijective (Ψ p) (hΨd p) ψ (fun m a b hab => ?_) hb
  obtain ⟨α, hα, hαa⟩ := hA.surj p (m - p) m (by omega) (fun j => (a j).1)
  refine hψ (m - p) m (by omega) α (fun j => hα j trivial) a b (fun j => (congrFun hαa j).symm) ?_
  rw [hab, ← hαa, hΨ p _ _ _ α hα]

theorem isColumns_total (D : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [D.HasTotal (ComplexShape.up ℤ)] (hD : ∀ p k, 0 < p ∨ 0 < k → IsZero ((D.X p).X k)) :
    IsColumns (D.total (ComplexShape.up ℤ)) D.X (fun p k t h => D.ιTotal (ComplexShape.up ℤ) p k t h) where
  ext t Y f hf := HomologicalComplex₂.total.hom_ext _ fun p k h => by rw [comp_zero]; exact hf p k h
  desc p k t h Y g := by
    refine ⟨D.totalDesc fun c l h' => if hc : c = p then
      eqToHom (by
        obtain rfl : l = k := by
          have : c + l = t := h'
          omega
        rw [hc]) ≫ g else 0, ?_, fun c l h' hc => ?_⟩
    · rw [HomologicalComplex₂.ι_totalDesc]; simp
    · rw [HomologicalComplex₂.ι_totalDesc, dif_neg hc]
  diff p k t k' t' h h' hk Y f hf := by
    rw [HomologicalComplex₂.total_d, Preadditive.add_comp, Preadditive.comp_add, HomologicalComplex₂.ι_D₁_assoc,
      HomologicalComplex₂.ι_D₂_assoc,
      D.d₁_eq _ (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) k t' (show p + 1 + k = t' by omega),
      D.d₂_eq _ p (show (ComplexShape.up ℤ).Rel k k' from hk) t' h', Linear.units_smul_comp, Linear.units_smul_comp,
      Category.assoc, Category.assoc, hf (p + 1) k _ (by omega), comp_zero, smul_zero, zero_add]
    rfl
  isZero := hD

variable [HasZeroObject C]

def ιTerm (L : CochainComplex C ℤ) (p k t : ℤ) (h : p + k = t) :
    ((CochainComplex.singleFunctor C 0).obj (L.X p)).X k ⟶ L.X t :=
  if hk : k = 0 then (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (L.X p) k hk).hom ≫
    (L.XIsoOfEq (show p = t by omega)).hom else 0

theorem ιTerm_zero (L : CochainComplex C ℤ) (p : ℤ) (h : p + 0 = p) :
    ιTerm L p 0 p h = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (L.X p)).hom := by
  rw [ιTerm, dif_pos rfl]
  exact Category.comp_id _

theorem eq_zero_of_ιTerm {L : CochainComplex C ℤ} {p : ℤ} {h : p + 0 = p} {Y : C} {f : L.X p ⟶ Y}
    (hf : ιTerm L p 0 p h ≫ f = 0) : f = 0 := by
  rw [ιTerm_zero] at hf
  exact (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (L.X p)).inv_hom_id_assoc f).symm.trans
    (congrArg (fun g => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (L.X p)).inv ≫ g) hf)).trans comp_zero

theorem ιTerm_ne (L : CochainComplex C ℤ) (p k t : ℤ) (h : p + k = t) (hk : k ≠ 0) : ιTerm L p k t h = 0 :=
  dif_neg hk

theorem isColumns_terms (L : CochainComplex C ℤ) [L.IsStrictlyLE 0] :
    IsColumns L (fun p => (CochainComplex.singleFunctor C 0).obj (L.X p)) (ιTerm L) where
  ext t Y f hf := by
    have := hf t 0 (add_zero t)
    exact eq_zero_of_ιTerm this
  desc p k t h Y g := by
    by_cases hk : k = 0
    · subst hk
      obtain rfl : t = p := by omega
      refine ⟨(HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (L.X t)).inv ≫ g, ?_, fun c l h' hc => ?_⟩
      · rw [ιTerm_zero]; exact Iso.hom_inv_id_assoc _ _
      · rw [ιTerm_ne _ _ _ _ _ (by omega), zero_comp]
    · exact ⟨0, (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (L.X p) k hk).eq_of_src _ _,
        fun _ _ _ _ => comp_zero⟩
  diff p k t k' t' h h' hk Y f hf := by
    have h1 : ((CochainComplex.singleFunctor C 0).obj (L.X p)).d k k' = 0 := rfl
    rw [h1, zero_comp, smul_zero]
    by_cases hk0 : k = 0
    · have := hf t' 0 (add_zero t') (by omega)
      rw [eq_zero_of_ιTerm this, comp_zero, comp_zero]
    · rw [ιTerm_ne _ _ _ _ _ hk0, zero_comp]
  isZero p k h := by
    by_cases hk : k = 0
    · exact (L.isZero_of_isStrictlyLE 0 p (by omega)).of_iso
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (L.X p) k hk)
    · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (L.X p) k hk

end Columns

section Sheaves
open GlobalTheory.EtC

theorem bijective_total_of_terms : ∀ (R : Type) [CommRing R] (D : HomologicalComplex₂ (Shv R) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [D.HasTotal (ComplexShape.up ℤ)], (∀ p k, 0 < p ∨ 0 < k → IsZero ((D.X p).X k)) →
    ∀ (L : Cx R) [L.IsStrictlyLE 0] {J : Type} [Finite J] (Ij : J → Cx R) [∀ j, (Ij j).IsStrictlyGE 0]
      (I : Cx R) [I.IsStrictlyGE 0] (e : J → ℤ)
      (Φ : ∀ n, (∀ j, Cochain L (Ij j) (n - e j)) →+ Cochain (D.total (ComplexShape.up ℤ)) I n),
    (∀ n m, n + 1 = m → ∀ α, Φ m (fun j => δ (n - e j) (m - e j) (α j)) = δ n m (Φ n α)) →
    (∀ (p n : ℤ) (α : ∀ j, Cochain L (Ij j) (n - e j)), (∀ j c q hq, p < c → (α j).v c q hq = 0) →
      ∀ (c k t : ℤ) (h : c + k = t) q hq, p < c → D.ιTotal (ComplexShape.up ℤ) c k t h ≫ (Φ n α).v t q hq = 0) →
    (∀ p ≤ (0 : ℤ), ∃ ψ : ∀ m, (∀ j, CohomologyClass (sgl (L.X p)) (Ij j) (m - e j)) → CohomologyClass (D.X p) I m,
      (∀ m, Function.Bijective (ψ m)) ∧
      ∀ n m, n + p = m → ∀ α : ∀ j, Cochain L (Ij j) (n - e j), (∀ j c q hq, p < c → (α j).v c q hq = 0) →
        ∀ (a : ∀ j, Cocycle (sgl (L.X p)) (Ij j) (m - e j)) (b : Cocycle (D.X p) I m),
          (∀ j q hq hq', sglι (L.X p) ≫ (a j).1.v 0 q hq = (α j).v p q hq') →
          (∀ (k t : ℤ) (h : p + k = t) q hq hq',
            b.1.v k q hq = D.ιTotal (ComplexShape.up ℤ) p k t h ≫ (Φ n α).v t q hq') →
          ψ m (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b) →
    ∀ (n : ℤ) (φ : (∀ j, CohomologyClass L (Ij j) (n - e j)) → CohomologyClass (D.total (ComplexShape.up ℤ)) I n),
      (∀ (a : ∀ j, Cocycle L (Ij j) (n - e j)) (b : Cocycle (D.total (ComplexShape.up ℤ)) I n),
        b.1 = Φ n (fun j => (a j).1) → φ (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b) →
      Function.Bijective φ := by
  intro R _ D _ hD L _ J _ Ij _ I _ e Φ hd hF hG n φ hφ
  have hv : ∀ (p n : ℤ) (K : Cx R) (α : Cochain L K n), α ∈ van (ιTerm L) K p n → ∀ c q hq, p < c → α.v c q hq = 0 := by
    intro p n K α hα c q hq hc
    have := hα c 0 c (add_zero c) q hq hc
    exact eq_zero_of_ιTerm this
  refine bijective_of_columns (isColumns_terms L) (isColumns_total D hD) Ij I e Φ hd
    (fun p n α hα => hF p n α fun j => hv p _ _ _ (hα j)) (fun p hp => ?_) n φ hφ
  obtain ⟨ψ, hb, hψ⟩ := hG p hp
  refine ⟨ψ, hb, fun n m h α hα a b ha hb => hψ n m h α (fun j => hv p _ _ _ (hα j)) a b
    (fun j q hq hq' => ?_) (fun k t ht q hq hq' => ?_)⟩
  · rw [ha j, restr_v _ _ p _ _ _ _ 0 p q (add_zero p) hq hq', ιTerm_zero]
    exact Iso.inv_hom_id_assoc _ _
  · rw [hb, restr_v _ _ p _ _ _ _ k t q ht hq hq']

end Sheaves

section Totals
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

end Totals

end GlobalTheory.ColFilt

end
