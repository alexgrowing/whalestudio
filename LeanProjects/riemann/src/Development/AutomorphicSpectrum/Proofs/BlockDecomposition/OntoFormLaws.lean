import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
open CrystallineSemistableComparison.Onto

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.OntoForms

open exteriorPower

theorem mem_of_span {R M X ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup X]
    [Module R X] [DecidableEq ι] (m : MultilinearMap R (fun _ : ι => M) X) (P : Submodule R X)
    (S : ι → Set M) (U : Finset ι) (hS : ∀ i ∈ U, Submodule.span R (S i) = ⊤)
    (h : ∀ v, (∀ j, v j ∈ S j) → m v ∈ P) :
    ∀ v, (∀ j, j ∉ U → v j ∈ S j) → m v ∈ P := by
  induction U using Finset.induction_on with
  | empty => intro v hv; exact h v fun j => hv j (by simp)
  | insert i U hi ih =>
    intro v hv
    have ih' := ih (fun j hj => hS j (Finset.mem_insert_of_mem hj))
    have hle : Submodule.span R (S i) ≤ P.comap (m.toLinearMap v i) := by
      rw [Submodule.span_le]
      intro x hx
      refine ih' _ fun j hj => ?_
      by_cases hji : j = i
      · subst hji; simpa using hx
      · rw [Function.update_of_ne hji]; exact hv j (by simp [hji, hj])
    have h3 : v i ∈ P.comap (m.toLinearMap v i) :=
      hle (by rw [hS i (Finset.mem_insert_self _ _)]; trivial)
    simpa using h3

theorem sub_mem_of_congr {R M X ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup X] [Module R X] [DecidableEq ι] (m : MultilinearMap R (fun _ : ι => M) X)
    (P : Submodule R X) (L : Submodule R M) (hP : ∀ v k, v k ∈ L → m v ∈ P) (U : Finset ι) :
    ∀ u u', (∀ k, k ∉ U → u k = u' k) → (∀ k, u k - u' k ∈ L) → m u - m u' ∈ P := by
  induction U using Finset.induction_on with
  | empty =>
    intro u u' h1 _
    have : u = u' := funext fun k => h1 k (by simp)
    simp [this]
  | insert i U hi ih =>
    intro u u' h1 h2
    have e : m u - m (Function.update u i (u' i)) = m (Function.update u i (u i - u' i)) := by
      rw [MultilinearMap.map_update_sub, Function.update_eq_self]
    have a1 : m u - m (Function.update u i (u' i)) ∈ P := by
      rw [e]; exact hP _ i (by simpa using h2 i)
    have a2 : m (Function.update u i (u' i)) - m u' ∈ P := by
      refine ih _ _ (fun k hk => ?_) (fun k => ?_)
      · by_cases hki : k = i
        · subst hki; simp
        · rw [Function.update_of_ne hki]; exact h1 k (by simp [hki, hk])
      · by_cases hki : k = i
        · subst hki; simp
        · rw [Function.update_of_ne hki]; exact h2 k
    simpa using P.add_mem a1 a2

theorem exists_module {R S Q : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hs : Function.Surjective (algebraMap R S)) [AddCommGroup Q] [Module R Q]
    (hI : ∀ c : R, algebraMap R S c = 0 → ∀ q : Q, c • q = 0) :
    ∃ inst : Module S Q, ∀ (c : R) (q : Q), inst.toSMul.smul (algebraMap R S c) q = c • q := by
  have hk : ∀ c c' : R, algebraMap R S c = algebraMap R S c' → ∀ q : Q, c • q = c' • q := by
    intro c c' h q
    have := hI (c - c') (by simp [h]) q
    rwa [sub_smul, sub_eq_zero] at this
  let σ := Function.surjInv hs
  have hσ : ∀ b, algebraMap R S (σ b) = b := Function.surjInv_eq hs
  refine ⟨{ smul := fun b q => σ b • q
            one_smul := fun q => ?_
            mul_smul := fun b b' q => ?_
            smul_zero := fun b => smul_zero _
            smul_add := fun b q q' => smul_add _ _ _
            add_smul := fun b b' q => ?_
            zero_smul := fun q => ?_ }, fun c q => ?_⟩
  case refine_1 =>
    change σ (b * b') • q = σ b • σ b' • q
    rw [← mul_smul]; exact hk _ _ (by simp [hσ]) q
  case refine_2 =>
    change σ 1 • q = q
    rw [hk (σ 1) 1 (by simp [hσ]), one_smul]
  case refine_3 =>
    change σ (b + b') • q = σ b • q + σ b' • q
    rw [← add_smul]; exact hk _ _ (by simp [hσ]) q
  case refine_4 =>
    change σ 0 • q = 0
    rw [hk (σ 0) 0 (by simp [hσ]), zero_smul]
  case refine_5 =>
    change σ (algebraMap R S c) • q = c • q
    exact hk _ _ (by simp [hσ]) q

theorem eq_zero_of_map {A B M N Q : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (hs : Function.Surjective (algebraMap A B)) [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] [Module B N] [IsScalarTower A B N] [AddCommGroup Q] [Module A Q] [Module B Q]
    [IsScalarTower A B Q] (f : M →ₗ[A] N) (hf : Function.Surjective f) (a : ℕ)
    (p : ⋀[A]^a M →ₗ[A] Q)
    (hp : ∀ (v : Fin a → M) k, f (v k) = 0 → p (ιMulti A a v) = 0)
    (T : ⋀[A]^a M →ₗ[A] ⋀[B]^a N)
    (hT : ∀ v, T (ιMulti A a v) = ιMulti B a fun k => f (v k))
    (ω : ⋀[A]^a M) (h0 : T ω = 0) : p ω = 0 := by
  let s := Function.surjInv hf
  have hs' : ∀ x, f (s x) = x := Function.surjInv_eq hf
  have cong : ∀ u u' : Fin a → M, (∀ k, f (u k) = f (u' k)) →
      p (ιMulti A a u) = p (ιMulti A a u') := by
    intro u u' h
    rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker]
    exact sub_mem_of_congr (ιMulti A a (M := M)).toMultilinearMap (LinearMap.ker p)
      (LinearMap.ker f) (fun v k hv => hp v k hv) Finset.univ u u' (by simp)
      (fun k => by simp [h k])
  have hcomp : ∀ (v : Fin a → N) (i : Fin a) (y : N),
      (fun k => s (Function.update v i y k)) = Function.update (fun k => s (v k)) i (s y) :=
    fun v i y => funext fun k => Function.apply_update (fun _ => s) v i y k
  let F : N [⋀^Fin a]→ₗ[B] Q :=
    { toFun := fun v => p (ιMulti A a fun k => s (v k))
      map_update_add' := by
        intro inst v i x y
        obtain rfl : inst = instDecidableEqFin a := Subsingleton.elim _ _
        change p (ιMulti A a fun k => s (Function.update v i (x + y) k)) =
          p (ιMulti A a fun k => s (Function.update v i x k)) +
          p (ιMulti A a fun k => s (Function.update v i y k))
        rw [hcomp, hcomp, hcomp, ← map_add, ← AlternatingMap.map_update_add]
        refine cong _ _ fun k => ?_
        by_cases hki : k = i
        · subst hki; simp [hs']
        · simp [Function.update_of_ne hki]
      map_update_smul' := by
        intro inst v i b x
        obtain rfl : inst = instDecidableEqFin a := Subsingleton.elim _ _
        obtain ⟨c, rfl⟩ := hs b
        change p (ιMulti A a fun k => s (Function.update v i (algebraMap A B c • x) k)) =
          algebraMap A B c • p (ιMulti A a fun k => s (Function.update v i x k))
        rw [hcomp, hcomp, algebraMap_smul, algebraMap_smul, ← map_smul, ← AlternatingMap.map_update_smul]
        refine cong _ _ fun k => ?_
        by_cases hki : k = i
        · subst hki; simp [hs']
        · simp [Function.update_of_ne hki]
      map_eq_zero_of_eq' := by
        intro v i j h hij
        change p (ιMulti A a fun k => s (v k)) = 0
        rw [(ιMulti A a (M := M)).map_eq_zero_of_eq (fun k => s (v k)) (congrArg s h) hij, map_zero] }
  let ψ : ⋀[B]^a N →ₗ[B] Q := alternatingMapLinearEquiv F
  have hψ : (ψ.restrictScalars A) ∘ₗ T = p := by
    refine exteriorPower.linearMap_ext ?_
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, hT]
    change ψ (ιMulti B a fun k => f (v k)) = _
    rw [alternatingMapLinearEquiv_apply_ιMulti]
    exact cong _ _ fun k => hs' _
  have := LinearMap.congr_fun hψ ω
  simpa [h0] using this.symm

theorem ker_le (K A B : Type*) [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [Algebra A B] [IsScalarTower K A B] (hs : Function.Surjective (algebraMap A B))
    (L : Submodule A Ω[A⁄K])
    (h1 : ∀ i, algebraMap A B i = 0 → KaehlerDifferential.D K A i ∈ L)
    (h2 : ∀ c, algebraMap A B c = 0 → ∀ w : Ω[A⁄K], c • w ∈ L) :
    LinearMap.ker (KaehlerDifferential.map K K A B) ≤ L := by
  classical
  rw [KaehlerDifferential.ker_map_of_surjective K A B hs]
  rintro _ ⟨c, hc, rfl⟩
  let σ := Function.surjInv hs
  have hσ : ∀ b, algebraMap A B (σ b) = b := Function.surjInv_eq hs
  have hd : ∀ b, algebraMap A B (Finsupp.mapDomain (algebraMap A B) c b) = 0 := by
    intro b
    have := DFunLike.congr_fun (LinearMap.mem_ker.mp hc) b
    simpa using this
  have e2 : Finsupp.linearCombination A (fun b => KaehlerDifferential.D K A (σ b))
      (Finsupp.mapDomain (algebraMap A B) c) ∈ L := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact Submodule.sum_mem _ fun b _ => h2 _ (hd b) _
  have e1 : Finsupp.linearCombination A (KaehlerDifferential.D K A) c -
      Finsupp.linearCombination A (fun b => KaehlerDifferential.D K A (σ b))
        (Finsupp.mapDomain (algebraMap A B) c) ∈ L := by
    rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
      Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun x _ => ?_
    simp only [Function.comp_apply]
    rw [← smul_sub, ← map_sub]
    exact L.smul_mem _ (h1 _ (by simp [hσ]))
  simpa using L.add_mem e1 e2

theorem mem_of_map_eq_zero {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (hs : Function.Surjective (algebraMap A B)) [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] [Module B N] [IsScalarTower A B N] (f : M →ₗ[A] N)
    (hf : Function.Surjective f) (a : ℕ) (P : Submodule A (⋀[A]^a M))
    (hP : ∀ (v : Fin a → M) k, f (v k) = 0 → ιMulti A a v ∈ P)
    (hI : ∀ c : A, algebraMap A B c = 0 → ∀ ω : ⋀[A]^a M, c • ω ∈ P)
    (T : ⋀[A]^a M →ₗ[A] ⋀[B]^a N)
    (hT : ∀ v, T (ιMulti A a v) = ιMulti B a fun k => f (v k))
    (ω : ⋀[A]^a M) (h0 : T ω = 0) : ω ∈ P := by
  have hQ : ∀ c : A, algebraMap A B c = 0 → ∀ q : (⋀[A]^a M) ⧸ P, c • q = 0 := by
    intro c hc q
    obtain ⟨ω', rfl⟩ := P.mkQ_surjective q
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hI c hc ω'
  obtain ⟨inst, hinst⟩ := exists_module hs hQ
  letI := inst
  haveI : IsScalarTower A B ((⋀[A]^a M) ⧸ P) := .of_algebraMap_smul hinst
  have h := eq_zero_of_map hs f hf a P.mkQ
    (fun v k hv => by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hP v k hv) T hT ω h0
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A] {a : ℕ}

theorem smul_form (c g₀ : A) (g : Fin a → A) : c • form K g₀ g = form K (c * g₀) g := by
  simp [form, mul_smul]

variable (K A a) in

theorem span_forms : Submodule.span K {ω : Om K A a | ∃ g₀ g, ω = form K g₀ g} = ⊤ := by
  classical
  set S := Submodule.span K {ω : Om K A a | ∃ g₀ g, ω = form K g₀ g} with hS
  have hsm : ∀ (c : A) x, x ∈ S → c • x ∈ S := by
    intro c x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨g₀, g, rfl⟩ := h
      exact Submodule.subset_span ⟨c * g₀, g, smul_form c g₀ g⟩
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact S.add_mem hx hy
    | smul k x _ hx => rw [smul_comm]; exact S.smul_mem k hx
  let S' : Submodule A (Om K A a) :=
    { carrier := S
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      smul_mem' := hsm }
  have hι : ∀ v, ιMulti A a v ∈ S' := fun v =>
    mem_of_span (ιMulti A a (M := Ω[A⁄K])).toMultilinearMap S'
      (fun _ => Set.range (KaehlerDifferential.D K A)) Finset.univ
      (fun _ _ => KaehlerDifferential.span_range_derivation K A)
      (fun v hv => by
        choose g hg using hv
        have hv' : v = fun k => KaehlerDifferential.D K A (g k) := funext fun k => (hg k).symm
        subst hv'
        exact Submodule.subset_span ⟨1, g, by simp [form]⟩)
      v (by simp)
  have hle : Submodule.span A (Set.range (ιMulti A a (M := Ω[A⁄K]))) ≤ S' := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact hι v
  rw [ιMulti_span] at hle
  rw [eq_top_iff]
  intro ω _
  exact hle (Submodule.mem_top (x := ω))

theorem smul_mem_relOm (I : Ideal A) {c : A} (hc : c ∈ I) (ω : Om K A a) :
    c • ω ∈ relOm K I a := by
  have hω : ω ∈ Submodule.span K {ω : Om K A a | ∃ g₀ g, ω = form K g₀ g} := by
    rw [span_forms]; trivial
  induction hω using Submodule.span_induction with
  | mem x h =>
    obtain ⟨g₀, g, rfl⟩ := h
    rw [smul_form]
    exact Submodule.subset_span ⟨_, g, Or.inl (I.mul_mem_right _ hc), rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul k x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_of_tower_mem _ k hx

theorem iota_mem_relOm_of_D (I : Ideal A) {i : A} (hi : i ∈ I) (k : Fin a) (v : Fin a → Ω[A⁄K])
    (hv : v k = KaehlerDifferential.D K A i) : ιMulti A a v ∈ relOm K I a := by
  refine mem_of_span (ιMulti A a (M := Ω[A⁄K])).toMultilinearMap (relOm K I a)
    (fun j => {x | ∃ g, x = KaehlerDifferential.D K A g ∧ (j = k → g = i)})
    (Finset.univ.erase k) (fun j hj => ?_) (fun v hv => ?_) v (fun j hj => ?_)
  · have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    have : {x | ∃ g, x = KaehlerDifferential.D K A g ∧ (j = k → g = i)} =
        Set.range (KaehlerDifferential.D K A) := by
      ext x
      constructor
      · rintro ⟨g, rfl, -⟩; exact ⟨g, rfl⟩
      · rintro ⟨g, rfl⟩; exact ⟨g, rfl, fun h => absurd h hjk⟩
    rw [this]
    exact KaehlerDifferential.span_range_derivation K A
  · choose g hg hg' using hv
    have hv' : v = fun k => KaehlerDifferential.D K A (g k) := funext hg
    subst hv'
    exact Submodule.subset_span ⟨1, g, Or.inr ⟨k, by rw [hg' k rfl]; exact hi⟩, by simp [form]⟩
  · have hjk : j = k := by simpa using hj
    subst hjk
    exact ⟨i, hv, fun _ => rfl⟩

theorem iota_mem_relOm {B : Type} [CommRing B] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    (hs : Function.Surjective (algebraMap A B)) (I : Ideal A)
    (hI : ∀ c, algebraMap A B c = 0 → c ∈ I) (v : Fin a → Ω[A⁄K]) (k : Fin a)
    (hv : KaehlerDifferential.map K K A B (v k) = 0) : ιMulti A a v ∈ relOm K I a := by
  have hle := ker_le K A B hs
    ((relOm K I a).comap ((ιMulti A a (M := Ω[A⁄K])).toMultilinearMap.toLinearMap v k))
    (fun i hi => iota_mem_relOm_of_D I (hI i hi) k _ (by simp))
    (fun c hc w => by
      simp only [Submodule.mem_comap, map_smul]
      exact smul_mem_relOm I (hI c hc) _)
  have h := hle (LinearMap.mem_ker.mpr hv)
  simpa using h

theorem formLaws : FormLaws := by
  intro K A B _ _ _ _ _ a
  refine ⟨span_forms K A a, fun φ => ?_⟩
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  let T : Om K A a →ₗ[A] Om K B a := exteriorPower.alternatingMapLinearEquiv
    { ((exteriorPower.ιMulti B a (M := Ω[B⁄K])).toMultilinearMap.restrictScalars A).compLinearMap
        fun _ => KaehlerDifferential.map K K A B with
      map_eq_zero_of_eq' := fun v i j h hij =>
        (exteriorPower.ιMulti B a (M := Ω[B⁄K])).map_eq_zero_of_eq
          (fun k => KaehlerDifferential.map K K A B (v k)) (congrArg _ h) hij }
  have hTo : ∀ ω, omMap φ a ω = T ω := fun _ => rfl
  have hT : ∀ v, T (ιMulti A a v) = ιMulti B a fun k => KaehlerDifferential.map K K A B (v k) :=
    fun v => alternatingMapLinearEquiv_apply_ιMulti _ _
  have hφ : ∀ x, algebraMap A B x = φ x := fun _ => rfl
  have hs : Function.Surjective φ → Function.Surjective (algebraMap A B) := fun h => h
  have h2 : ∀ g₀ (g : Fin a → A), omMap φ a (form K g₀ g) = form K (φ g₀) fun k => φ (g k) := by
    intro g₀ g
    have e : (fun k => KaehlerDifferential.map K K A B (KaehlerDifferential.D K A (g k))) =
        fun k => KaehlerDifferential.D K B (φ (g k)) :=
      funext fun k => KaehlerDifferential.map_D K K A B (g k)
    rw [hTo]
    unfold form
    rw [map_smul, hT, e, ← hφ g₀, algebraMap_smul]
  have h3 : ∀ (c : A) ω, omMap φ a (c • ω) = φ c • omMap φ a ω := by
    intro c ω
    rw [hTo, hTo, map_smul, ← hφ c, algebraMap_smul]
  refine ⟨h2, h3, fun hsurj => ⟨?_, fun ω => ⟨fun h0 => ?_, fun hω => ?_⟩⟩⟩
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← span_forms K B a, Submodule.span_le]
    rintro _ ⟨g₀, g, rfl⟩
    obtain ⟨c₀, rfl⟩ := hsurj g₀
    choose c hc using fun k => hsurj (g k)
    refine ⟨form K c₀ c, ?_⟩
    rw [h2]
    simp only [hc]
  · exact mem_of_map_eq_zero (hs hsurj) (KaehlerDifferential.map K K A B)
      (KaehlerDifferential.map_surjective_of_surjective K K A B (hs hsurj)) a _
      (fun v k hv => iota_mem_relOm (hs hsurj) _ (fun c hc => RingHom.mem_ker.mpr hc) v k hv)
      (fun c hc ω => smul_mem_relOm _ (RingHom.mem_ker.mpr hc) ω) T hT ω h0
  · induction hω using Submodule.span_induction with
    | mem x h =>
      obtain ⟨g₀, g, h, rfl⟩ := h
      rw [h2]
      rcases h with h | ⟨k, hk⟩
      · rw [RingHom.mem_ker.mp h]; simp [form]
      · have hk' : φ (g k) = 0 := RingHom.mem_ker.mp hk
        unfold form
        rw [(ιMulti B a (M := Ω[B⁄K])).map_coord_zero k (by simp [hk']), smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [h3, hx, smul_zero]

end GlobalTheory.CompanionTheory.OntoForms

end
