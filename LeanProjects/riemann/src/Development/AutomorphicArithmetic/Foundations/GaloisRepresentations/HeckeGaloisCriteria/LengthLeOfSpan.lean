import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.ActEqZeroOfQK

noncomputable section

namespace UpperTheory.GalC.Alg

open Formalism.BasicNotions TensorProduct

theorem length_le_of_span {O Q C : Type} [CommRing O] [AddCommGroup Q] [Module O Q] [AddCommGroup C] [Module O C] {m : ℕ}
    (b : Fin m → Q) (hb : Submodule.span O (Set.range b) = ⊤) (π : Q →ₗ[O] C) (hπ : Function.Surjective π) (A : O)
    (hA : ∀ q, A • π q = 0) : Module.length O C ≤ m * Module.length O (O ⧸ Ideal.span {A}) := by
  classical
  have hI : ∀ i, (Ideal.span {A} : Submodule O O) ≤ LinearMap.ker (LinearMap.toSpanSingleton O C (π (b i))) := by
    intro i x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    simp [LinearMap.mem_ker, mul_smul, hA]
  let g : (Fin m → O ⧸ Ideal.span {A}) →ₗ[O] C :=
    ∑ i, ((Ideal.span {A} : Submodule O O).liftQ (LinearMap.toSpanSingleton O C (π (b i))) (hI i)).comp
      (LinearMap.proj i)
  have hg : Function.Surjective g := by
    intro c
    obtain ⟨q, rfl⟩ := hπ c
    have hq : q ∈ Submodule.span O (Set.range b) := hb ▸ Submodule.mem_top
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp hq
    refine ⟨fun i => Submodule.Quotient.mk (r i), ?_⟩
    simp [g, ← hr, map_sum, map_smul]
    exact Finset.sum_congr rfl fun i _ => rfl
  calc Module.length O C ≤ Module.length O (Fin m → O ⧸ Ideal.span {A}) := Module.length_le_of_surjective g hg
    _ = m * Module.length O (O ⧸ Ideal.span {A}) := by simp

variable {O X M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
  (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M) (S : Set X)
  [Fintype X] (hs : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y)

include hs in
theorem decomp : ∃ (f : X → T) (d : O), d ≠ 0 ∧ (∀ x y, y ≠ x → (f x : X → O) y = 0) ∧
    ∀ v : FractionRing O ⊗[O] M, d • v = ∑ x, (act (f x)).baseChange (FractionRing O) v := by
  classical
  choose f hf0 hf1 using exists_sep T hs
  set d : O := ∏ x, (f x : X → O) x with hd
  let g : X → T := fun x => (∏ y ∈ Finset.univ.erase x, (f y : X → O) y) • f x
  have hg0 : ∀ x y, y ≠ x → (g x : X → O) y = 0 := by
    intro x y hyx
    simp [g, hf1 x y hyx]
  have hsum : (∑ x, g x) = d • (1 : T) := by
    apply Subtype.ext
    funext z
    simp only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul,
      OneMemClass.coe_one, Pi.one_apply, mul_one]
    rw [Finset.sum_eq_single z]
    · simp only [g, SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
      rw [hd, Finset.prod_erase_mul _ _ (Finset.mem_univ z)]
    · intro x _ hxz
      exact hg0 x z (Ne.symm hxz)
    · intro h
      exact absurd (Finset.mem_univ z) h
  refine ⟨g, d, ?_, hg0, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun x _ => hf0 x
  · intro v
    have hlin : ∀ s : Finset X, ∑ x ∈ s, (act (g x)).baseChange (FractionRing O) v =
        (act (∑ x ∈ s, g x)).baseChange (FractionRing O) v := by
      intro s
      refine Finset.induction_on s (by simp) ?_
      intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, map_add, LinearMap.baseChange_add, LinearMap.add_apply]
    rw [hlin, hsum, map_smul, map_one, LinearMap.baseChange_smul, LinearMap.smul_apply]
    simp

include hs in

theorem qK_eq_zero_iff {v : FractionRing O ⊗[O] M} : qK T act S v = 0 ↔ v ∈ ⨆ x ∈ Sᶜ, heckeEig T act x := by
  constructor
  · intro hv
    obtain ⟨g, d, hd, hg0, hdec⟩ := decomp T act hs
    have hdv : (algebraMap O (FractionRing O) d) • v ∈ ⨆ x ∈ Sᶜ, heckeEig T act x := by
      rw [algebraMap_smul, hdec v]
      refine Submodule.sum_mem _ fun x _ => ?_
      by_cases hx : x ∈ S
      · rw [act_eq_zero_of_qK T act S hv (g x) (fun y hy => hg0 x y (fun h => hy (by rw [h]; exact hx)))]
        exact Submodule.zero_mem _
      · exact (le_iSup₂ (f := fun x (_ : x ∈ Sᶜ) => heckeEig T act x) x hx) (sep_mem T act (hg0 x) v)
    have hd' : algebraMap O (FractionRing O) d ≠ 0 := by
      simpa using (IsFractionRing.injective O (FractionRing O)).ne hd
    have := Submodule.smul_mem _ (algebraMap O (FractionRing O) d)⁻¹ hdv
    rwa [smul_smul, inv_mul_cancel₀ hd', one_smul] at this
  · intro hv
    refine (iSup₂_le (fun x hx => ?_) : (⨆ x ∈ Sᶜ, heckeEig T act x) ≤ LinearMap.ker (qK T act S)) hv
    intro u hu
    exact qK_out T act S hs hx hu

abbrev inL (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] : Submodule O (FractionRing O ⊗[O] M) :=
  LinearMap.range (TensorProduct.mk O (FractionRing O) M 1)

abbrev upL (Y : Set X) : Submodule O (FractionRing O ⊗[O] M) :=
  (⨆ x ∈ Y, heckeEig T act x).restrictScalars O ⊓ (inL O M ⊔ (⨆ x ∈ Yᶜ, heckeEig T act x).restrictScalars O)

abbrev lowL (Y : Set X) : Submodule O (FractionRing O ⊗[O] M) := inL O M ⊓ (⨆ x ∈ Y, heckeEig T act x).restrictScalars O

include hs in
theorem map_sum_le (Y : Set X) (Y' : Set S) (h : ∀ x : S, x.1 ∈ Y → x ∈ Y') {v : FractionRing O ⊗[O] M}
    (hv : v ∈ ⨆ x ∈ Y, heckeEig T act x) : qK T act S v ∈ ⨆ x ∈ Y', heckeEig (cutT T S) (cutAct T act S) x := by
  have key : (⨆ x ∈ Y, heckeEig T act x) ≤
      (⨆ x ∈ Y', heckeEig (cutT T S) (cutAct T act S) x).comap (qK T act S) := by
    refine iSup₂_le fun x hx => ?_
    intro u hu
    rw [Submodule.mem_comap]
    by_cases hxS : x ∈ S
    · exact (le_iSup₂ (f := fun (z : S) (_ : z ∈ Y') => heckeEig (cutT T S) (cutAct T act S) z) ⟨x, hxS⟩
        (h ⟨x, hxS⟩ hx)) (qK_mem T act S (x := ⟨x, hxS⟩) hu)
    · rw [qK_out T act S hs hxS hu]
      exact Submodule.zero_mem _
  exact key hv

omit [Fintype X] in
theorem finrank_sum_le [Module.Finite O M] (Z : Finset X) :
    Module.finrank (FractionRing O) ↥(⨆ x ∈ (Z : Set X), heckeEig T act x) ≤ ∑ x ∈ Z, heckeMult T act x := by
  classical
  unfold heckeMult
  refine Finset.induction_on Z (by simp) ?_
  intro a s ha ih
  rw [Finset.coe_insert, iSup_insert, Finset.sum_insert ha]
  exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

private theorem exists_ne_zero_smul_upL_mem_lowL (hs' : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) (Y : Set X) :
    ∃ d : O, d ≠ 0 ∧ ∀ u ∈ upL T act Y, d • u ∈ lowL T act Y := by
  classical
  obtain ⟨g, d, hd, hg0, hdec⟩ := decomp T act hs'
  refine ⟨d, hd, fun u hu => ?_⟩
  have hkill : ∀ (W : Set X) x, x ∉ W → ∀ w ∈ ⨆ y ∈ W, heckeEig T act y,
      (act (g x)).baseChange (FractionRing O) w = 0 := by
    intro W x hx w hw
    have hle : (⨆ y ∈ W, heckeEig T act y) ≤ LinearMap.ker ((act (g x)).baseChange (FractionRing O)) := by
      refine iSup₂_le fun y hy => ?_
      intro z hz
      rw [LinearMap.mem_ker, (mem_eig T act).mp hz (g x), hg0 x y (fun h => hx (by rw [← h]; exact hy)),
        map_zero, zero_smul]
    exact hle hw
  obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
  obtain ⟨l, hl, w, hw, hlw⟩ := Submodule.mem_sup.mp hu2
  obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hl
  rw [hdec u]
  refine Submodule.sum_mem _ fun x _ => ?_
  by_cases hx : x ∈ Y
  · have hw0 : (act (g x)).baseChange (FractionRing O) w = 0 := hkill Yᶜ x (fun h => h hx) w hw
    have hux : (act (g x)).baseChange (FractionRing O) u = (1 : FractionRing O) ⊗ₜ[O] (act (g x) m) := by
      rw [← hlw, map_add, hw0, add_zero, TensorProduct.mk_apply, LinearMap.baseChange_tmul]
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hux]
      exact LinearMap.mem_range.mpr ⟨act (g x) m, rfl⟩
    · exact (le_iSup₂ (f := fun y (_ : y ∈ Y) => heckeEig T act y) x hx) (sep_mem T act (hg0 x) u)
  · rw [hkill Y x hx u hu1]
    exact Submodule.zero_mem _

private theorem isNoetherian_upL [IsNoetherianRing O] [Module.Finite O M]
    (hs' : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) (Y : Set X) :
    IsNoetherian O ↥(upL T act Y) := by
  obtain ⟨d, hd, hdu⟩ := exists_ne_zero_smul_upL_mem_lowL T act hs' Y
  haveI hL : IsNoetherian O ↥(inL O M) :=
    isNoetherian_of_surjective (LinearMap.rangeRestrict (TensorProduct.mk O (FractionRing O) M 1))
      (LinearMap.range_rangeRestrict _)
  let ψ : ↥(upL T act Y) →ₗ[O] ↥(inL O M) :=
    LinearMap.codRestrict (inL O M) (d • (upL T act Y).subtype) (fun u => (Submodule.mem_inf.mp (hdu u u.2)).1)
  refine isNoetherian_of_injective ψ ?_
  intro u v huv
  have h1 : d • ((u : FractionRing O ⊗[O] M) - v) = 0 := by
    have this : d • (u : FractionRing O ⊗[O] M) = d • (v : FractionRing O ⊗[O] M) := congrArg Subtype.val huv
    rw [smul_sub, this, sub_self]
  rw [← algebraMap_smul (FractionRing O), smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd ((IsFractionRing.injective O (FractionRing O)).eq_iff.mp (h1.trans (map_zero _).symm)) hd
  · exact Subtype.ext (sub_eq_zero.mp h1)

private theorem smul_eq_of_mem_iSup_heckeEig_of_forall_eigen (Y : Set X)
    (φ : FractionRing O ⊗[O] M →ₗ[FractionRing O] FractionRing O ⊗[O] M) (c : FractionRing O)
    (h : ∀ x ∈ Y, ∀ u ∈ heckeEig T act x, φ u = c • u) {u : FractionRing O ⊗[O] M}
    (hu : u ∈ ⨆ x ∈ Y, heckeEig T act x) : φ u = c • u := by
  have hle : (⨆ x ∈ Y, heckeEig T act x) ≤ LinearMap.ker (φ - c • LinearMap.id) := by
    refine iSup₂_le fun x hx => ?_
    intro w hw
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, h x hx w hw, sub_self]
  have := hle hu
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at this

set_option maxHeartbeats 1000000 in
include hs in
theorem length_le [IsPrincipalIdealRing O] [Module.Finite O M] (Z : Finset X) (Y' : Set S) (hY : ∀ x : S, x ∈ Y' ↔ x.1 ∈ Z)
    (α : Module.End O M) (A : O) (hA : A ≠ 0)
    (h1 : ∀ x ∈ Z, ∀ u ∈ heckeEig T act x, α.baseChange (FractionRing O) u = A • u)
    (h0 : ∀ x, x ∉ S → ∀ u ∈ heckeEig T act x, α.baseChange (FractionRing O) u = 0) :
    Module.length O (↥(upL T act (Z : Set X)) ⧸ (lowL T act (Z : Set X)).comap (upL T act (Z : Set X)).subtype) ≤
      Module.length O (↥(upL (cutT T S) (cutAct T act S) Y') ⧸
        (lowL (cutT T S) (cutAct T act S) Y').comap (upL (cutT T S) (cutAct T act S) Y').subtype) +
      (∑ x ∈ Z, heckeMult T act x : ℕ) * Module.length O (O ⧸ Ideal.span {A}) := by
  classical
  haveI : IsNoetherian O ↥(upL T act (Z : Set X)) := isNoetherian_upL T act hs _
  have hY1 : ∀ x : S, x.1 ∈ (Z : Set X) → x ∈ Y' := fun x hx => (hY x).mpr hx
  have hY2 : ∀ x : S, x.1 ∈ (Z : Set X)ᶜ → x ∈ Y'ᶜ := fun x hx hx' => hx ((hY x).mp hx')
  have hqL : ∀ l ∈ inL O M, qK T act S l ∈ inL O (cutM T act S) := by
    intro l hl
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hl
    exact LinearMap.mem_range.mpr ⟨(outM T act S).mkQ m, by simp only [TensorProduct.mk_apply, qK_tmul]⟩
  have hup : ∀ u ∈ upL T act (Z : Set X), qK T act S u ∈ upL (cutT T S) (cutAct T act S) Y' := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
    refine Submodule.mem_inf.mpr ⟨map_sum_le T act S hs (Z : Set X) Y' hY1 hu1, ?_⟩
    obtain ⟨l, hl, w, hw, rfl⟩ := Submodule.mem_sup.mp hu2
    rw [map_add]
    exact Submodule.add_mem_sup (hqL l hl) (map_sum_le T act S hs (Z : Set X)ᶜ Y'ᶜ hY2 hw)
  have hlow : ∀ u ∈ lowL T act (Z : Set X), qK T act S u ∈ lowL (cutT T S) (cutAct T act S) Y' := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
    exact Submodule.mem_inf.mpr ⟨hqL u hu1, map_sum_le T act S hs (Z : Set X) Y' hY1 hu2⟩
  let U := upL T act (Z : Set X)
  let Lo := (lowL T act (Z : Set X)).comap U.subtype
  let U' := upL (cutT T S) (cutAct T act S) Y'
  let Lo' := (lowL (cutT T S) (cutAct T act S) Y').comap U'.subtype
  let Φ0 : ↥U →ₗ[O] ↥U' :=
    LinearMap.codRestrict U' (((qK T act S).restrictScalars O).comp U.subtype) (fun u => hup u u.2)
  have hΦ0 : Lo ≤ Lo'.comap Φ0 := fun u hu => hlow u hu
  let Φ : (↥U ⧸ Lo) →ₗ[O] (↥U' ⧸ Lo') := Lo.mapQ Lo' Φ0 hΦ0
  have hexact : Function.Exact (LinearMap.ker Φ).subtype Φ.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have hex := Module.length_eq_add_of_exact (LinearMap.ker Φ).subtype Φ.rangeRestrict
    (Submodule.subtype_injective _) (LinearMap.surjective_rangeRestrict Φ) hexact
  have hran : Module.length O ↥(LinearMap.range Φ) ≤ Module.length O (↥U' ⧸ Lo') :=
    Module.length_le_of_injective (LinearMap.range Φ).subtype (Submodule.subtype_injective _)
  have hKA : ∀ k ∈ LinearMap.ker Φ, A • k = 0 := by
    intro k hk
    obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective Lo k
    have hk' : Lo'.mkQ (Φ0 u) = 0 := LinearMap.mem_ker.mp hk
    have hq : Φ0 u ∈ Lo' := (Submodule.Quotient.mk_eq_zero _).mp hk'
    have hu1 : (u : FractionRing O ⊗[O] M) ∈ ⨆ x ∈ (Z : Set X), heckeEig T act x := (Submodule.mem_inf.mp u.2).1
    obtain ⟨hqL', -⟩ := Submodule.mem_inf.mp hq
    obtain ⟨m', hm⟩ := LinearMap.mem_range.mp hqL'
    obtain ⟨m0, rfl⟩ := Submodule.mkQ_surjective _ m'
    have hz : qK T act S ((u : FractionRing O ⊗[O] M) - (1 : FractionRing O) ⊗ₜ[O] m0) = 0 := by
      have hm2 : qK T act S (u : FractionRing O ⊗[O] M) = (1 : FractionRing O) ⊗ₜ[O] (outM T act S).mkQ m0 := hm.symm
      rw [map_sub, qK_tmul, hm2, sub_self]
    have hw := (qK_eq_zero_iff T act S hs).mp hz
    have hα1 : α.baseChange (FractionRing O) (u : FractionRing O ⊗[O] M) = A • (u : FractionRing O ⊗[O] M) := by
      have := smul_eq_of_mem_iSup_heckeEig_of_forall_eigen T act (Z : Set X) (α.baseChange (FractionRing O)) (algebraMap O (FractionRing O) A)
        (fun x hx w hw => by rw [h1 x hx w hw, algebraMap_smul]) hu1
      rwa [algebraMap_smul] at this
    have hα0 := smul_eq_of_mem_iSup_heckeEig_of_forall_eigen T act Sᶜ (α.baseChange (FractionRing O)) 0
        (fun x hx w hw => by rw [h0 x hx w hw, zero_smul]) hw
    have hAu : A • (u : FractionRing O ⊗[O] M) = (1 : FractionRing O) ⊗ₜ[O] α m0 := by
      rw [zero_smul, map_sub, sub_eq_zero, LinearMap.baseChange_tmul] at hα0
      rw [← hα1, hα0]
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show A • (u : FractionRing O ⊗[O] M) ∈ lowL T act (Z : Set X)
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hAu]
      exact LinearMap.mem_range.mpr ⟨α m0, rfl⟩
    · show A • (u : FractionRing O ⊗[O] M) ∈ ⨆ x ∈ (Z : Set X), heckeEig T act x
      rw [← algebraMap_smul (FractionRing O)]
      exact Submodule.smul_mem _ _ hu1
  have hK : Module.length O ↥(LinearMap.ker Φ) ≤
      (∑ x ∈ Z, heckeMult T act x : ℕ) * Module.length O (O ⧸ Ideal.span {A}) := by
    let P : Submodule O ↥U := (LinearMap.ker Φ).comap Lo.mkQ
    let π : ↥P →ₗ[O] ↥(LinearMap.ker Φ) := Lo.mkQ.restrict (fun x hx => hx)
    have hπ : Function.Surjective π := by
      intro k
      obtain ⟨y, hy⟩ := Submodule.mkQ_surjective Lo k.1
      exact ⟨⟨y, show Lo.mkQ y ∈ LinearMap.ker Φ from hy ▸ k.2⟩, Subtype.ext hy⟩
    have hA' : ∀ q, A • π q = 0 := fun q => Subtype.ext (hKA (Lo.mkQ q) q.2)
    haveI hV : Module.IsTorsionFree O (FractionRing O ⊗[O] M) :=
      Module.IsTorsionFree.trans_faithfulSMul O (FractionRing O) _
    haveI : Module.IsTorsionFree O ↥P :=
      Function.Injective.moduleIsTorsionFree (fun p : P => ((p : ↥U) : FractionRing O ⊗[O] M))
        (fun a b hab => Subtype.ext (Subtype.ext hab)) (fun r p => rfl)
    haveI : Module.Free O ↥P := Module.free_of_finite_type_torsion_free'
    let b := Module.finBasis O ↥P
    have hlen := length_le_of_span (fun i => b i) b.span_eq π hπ A hA'
    have hr : Module.finrank O ↥P ≤ ∑ x ∈ Z, heckeMult T act x := by
      have hinj : LinearMap.ker (U.subtype ∘ₗ P.subtype) = ⊥ :=
        LinearMap.ker_eq_bot.mpr (fun a c hac => Subtype.ext (Subtype.ext hac))
      have hv := b.linearIndependent.map' (U.subtype ∘ₗ P.subtype) hinj
      have hv' := hv.localization (FractionRing O) (nonZeroDivisors O)
      have hsub : Submodule.span (FractionRing O) (Set.range ((U.subtype ∘ₗ P.subtype) ∘ b)) ≤ ⨆ x ∈ (Z : Set X), heckeEig T act x := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact (Submodule.mem_inf.mp (b i : ↥U).2).1
      calc Module.finrank O ↥P = Fintype.card (Fin (Module.finrank O ↥P)) := (Fintype.card_fin _).symm
        _ = Module.finrank (FractionRing O) ↥(Submodule.span (FractionRing O) (Set.range ((U.subtype ∘ₗ P.subtype) ∘ b))) :=
          (finrank_span_eq_card hv').symm
        _ ≤ Module.finrank (FractionRing O) ↥(⨆ x ∈ (Z : Set X), heckeEig T act x) := Submodule.finrank_mono hsub
        _ ≤ ∑ x ∈ Z, heckeMult T act x := finrank_sum_le T act Z
    refine hlen.trans ?_
    have hr' : (Module.finrank O ↥P : ℕ∞) ≤ ((∑ x ∈ Z, heckeMult T act x : ℕ) : ℕ∞) := Nat.cast_le.mpr hr
    exact mul_le_mul_of_nonneg_right hr' zero_le
  rw [hex, add_comm]
  exact add_le_add hran hK

include hs in
theorem length_ne_top [IsDiscreteValuationRing O] [Module.Finite O M] (Z : Finset X) :
    Module.length O (↥(upL T act (Z : Set X)) ⧸ (lowL T act (Z : Set X)).comap (upL T act (Z : Set X)).subtype) ≠ ⊤ := by
  classical
  haveI : IsNoetherian O ↥(upL T act (Z : Set X)) := isNoetherian_upL T act hs _
  obtain ⟨d, hd, hdu⟩ := exists_ne_zero_smul_upL_mem_lowL T act hs (Z : Set X)
  obtain ⟨k, b, hb⟩ := Module.Finite.exists_fin (R := O) (M := ↥(upL T act (Z : Set X)))
  have hle := length_le_of_span b hb ((lowL T act (Z : Set X)).comap (upL T act (Z : Set X)).subtype).mkQ
    (Submodule.mkQ_surjective _) d (fun q => by
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hdu q q.2)
  have hfin : Module.length O (O ⧸ Ideal.span {d}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hd))
  exact ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.coe_ne_top k) hfin) hle

theorem lenUnit_le_add {O : Type} [CommRing O] (l : ℕ) {B C E : Type} [AddCommGroup B] [Module O B] [AddCommGroup C] [Module O C]
    [AddCommGroup E] [Module O E] (n : ℕ) (hE : Module.length O E ≠ ⊤) (hB : Module.length O C = ⊤ → Module.length O B = ⊤)
    (h : Module.length O B ≤ Module.length O C + n * Module.length O E) :
    lenUnit (O := O) l B ≤ lenUnit (O := O) l C + n * lenUnit (O := O) l E := by
  unfold lenUnit
  have key : ((Module.length O B).toNat : ℚ) ≤ (Module.length O C).toNat + n * (Module.length O E).toNat := by
    by_cases hC : Module.length O C = ⊤
    · rw [hB hC]
      simp only [ENat.toNat_top, Nat.cast_zero]
      positivity
    · obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hC
      obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hE
      rw [← hc, ← he] at h
      have h' : Module.length O B ≤ ((c + n * e : ℕ) : ℕ∞) := by
        push_cast
        exact h
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.coe_ne_top _) h')
      rw [← hk] at h'
      rw [← hk, ← hc, ← he]
      simp only [ENat.toNat_coe]
      have := ENat.coe_le_coe.mp h'
      exact_mod_cast this
  rw [mul_div_assoc', ← add_div]
  gcongr

end UpperTheory.GalC.Alg
