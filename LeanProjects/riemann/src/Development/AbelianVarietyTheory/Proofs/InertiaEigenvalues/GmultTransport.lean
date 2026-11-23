import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityQuotientAdditiveChain

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.SenAdd

section
variable {k A B : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]

theorem pow_mem (T : Module.End k A) (Q : Submodule k A) (hQ : ∀ y ∈ Q, T y ∈ Q) (x : k) (m : ℕ) :
    ∀ y ∈ Q, ((T - algebraMap k (Module.End k A) x) ^ m) y ∈ Q := by
  induction m with
  | zero => intro y hy; simpa using hy
  | succ m ih =>
    intro y hy
    rw [pow_succ, Module.End.mul_apply]
    apply ih
    rw [LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact Q.sub_mem (hQ y hy) (Q.smul_mem _ hy)

theorem mem_gen (T : Module.End k A) (Q : Submodule k A) (hQ : ∀ y ∈ Q, T y ∈ Q) (x : k) (y : A) :
    y ∈ (⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k A) x) ^ m)) ↔
      ∃ m : ℕ, ((T - algebraMap k (Module.End k A) x) ^ m) y ∈ Q := by
  have hm : Monotone fun m : ℕ => Q.comap ((T - algebraMap k (Module.End k A) x) ^ m) := by
    refine monotone_nat_of_le_succ fun m z hz => ?_
    rw [Submodule.mem_comap] at hz ⊢
    rw [pow_succ', Module.End.mul_apply]
    simpa using pow_mem T Q hQ x 1 _ hz
  exact Submodule.mem_iSup_of_directed _ hm.directed_le

theorem pow_comm (T : Module.End k A) (T' : Module.End k B) (h : A →ₗ[k] B) (hT : ∀ y, h (T y) = T' (h y))
    (x : k) (m : ℕ) (y : A) :
    h (((T - algebraMap k (Module.End k A) x) ^ m) y) = ((T' - algebraMap k (Module.End k B) x) ^ m) (h y) := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    congr 1
    simp [Module.algebraMap_end_apply, hT]

theorem gmult_transport (T : Module.End k A) (T' : Module.End k B) (h : A →ₗ[k] B)
    (hT : ∀ y, h (T y) = T' (h y)) (P Q : Submodule k A) (P' Q' : Submodule k B)
    (hP : ∀ y ∈ P, T y ∈ P) (hQP : Q ≤ P) (hQ' : ∀ y ∈ Q', T' y ∈ Q')
    (hmap : ∀ y ∈ P, h y ∈ P') (hker : ∀ y ∈ P, h y ∈ Q' ↔ y ∈ Q)
    (hsur : ∀ z ∈ P', ∃ y ∈ P, z - h y ∈ Q') (x : k) : gmult T P Q x = gmult T' P' Q' x := by
  have hQ : ∀ y ∈ Q, T y ∈ Q := fun y hy =>
    (hker _ (hP y (hQP hy))).1 (by rw [hT]; exact hQ' _ ((hker y (hQP hy)).2 hy))
  unfold gmult
  set G := P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k A) x) ^ m) with hG
  set G' := P' ⊓ ⨆ m : ℕ, Q'.comap ((T' - algebraMap k (Module.End k B) x) ^ m) with hG'
  have hGG : ∀ y ∈ G, h y ∈ G' := by
    rintro y ⟨hy, hy2⟩
    obtain ⟨m, hm⟩ := (mem_gen T Q hQ x y).1 hy2
    refine ⟨hmap y hy, (mem_gen T' Q' hQ' x _).2 ⟨m, ?_⟩⟩
    rw [← pow_comm T T' h hT]
    exact (hker _ (hQP hm)).2 hm
  let φ : G →ₗ[k] (G' ⧸ Q'.submoduleOf G') := (Q'.submoduleOf G').mkQ ∘ₗ h.restrict hGG
  have hk : Q.submoduleOf G = LinearMap.ker φ := by
    ext ⟨y, hy⟩
    rw [LinearMap.mem_ker]
    change y ∈ Q ↔ Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (hker y hy.1).symm
  have hs : Function.Surjective φ := by
    intro w
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨y, hy, hzy⟩ := hsur z hz.1
    obtain ⟨m, hm⟩ := (mem_gen T' Q' hQ' x z).1 hz.2
    have hyG : y ∈ G := by
      refine ⟨hy, (mem_gen T Q hQ x y).2 ⟨m, (hker _ (pow_mem T P hP x m y hy)).1 ?_⟩⟩
      rw [pow_comm T T' h hT]
      have := Q'.sub_mem hm (pow_mem T' Q' hQ' x m _ hzy)
      rwa [map_sub, sub_sub_cancel] at this
    refine ⟨⟨y, hyG⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [eq_comm, Submodule.Quotient.eq]
    exact hzy
  rw [hk]
  exact (φ.quotKerEquivOfSurjective hs).finrank_eq

end

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

omit [Module k V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in

theorem sh_one_le (N : Submodule k⟦X⟧ V) : sh 1 N ≤ N := by
  have := sh_le_sh_of_le (zero_le_one' ℤ) N
  rwa [sh_zero_eq] at this

theorem nab_mem_sh_one {l : ℕ} (R : RingPG k l) (g : V →ₗ[k] V) (hg : Semi R.γ g) (N : Submodule k⟦X⟧ V)
    (hN : CondC g N) : ∀ y ∈ sh 1 N, nab g y ∈ sh 1 N := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_sh_iff_exists.1 hy
  obtain ⟨κ, -, hκ⟩ := R.γ_v
  have hv := vv_ne_zero k
  have h1 := hN z hz
  have h2 : g z ∈ N := by simpa using N.add_mem (sh_one_le N h1) hz
  have h3 : vv k ^ (1 : ℤ) • (κ • g z) ∈ sh 1 N := mem_sh_iff_exists.2 ⟨_, N.smul_mem κ h2, rfl⟩
  have h4 : nab g (vv k ^ (1 : ℤ) • z) = (g z - z) - vv k ^ (1 : ℤ) • (κ • g z) := by
    rw [nab_apply_eq, zpow_one, hg, hκ, ← algebraMap_smul k⸨X⸩ κ, mul_smul, ← smul_sub, inv_smul_smul₀ hv,
      sub_smul, one_smul, smul_smul, mul_comm (vv k)]
    change g z - ((κ : k⸨X⸩) * vv k) • g z - z = g z - z - ((κ : k⸨X⸩) * vv k) • g z
    abel
  rw [h4]
  exact Submodule.sub_mem _ h1 h3

omit [IsScalarTower k k⸨X⸩ V] in

theorem finite_quot (N : Submodule k⟦X⟧ V) (hN : N.FG) :
    FiniteDimensional k (↥(N.restrictScalars k) ⧸
      ((sh 1 N).restrictScalars k).submoduleOf (N.restrictScalars k)) := by
  obtain ⟨s, hs⟩ := hN
  have hle : Submodule.span k (s : Set V) ≤ N.restrictScalars k :=
    Submodule.span_le.2 fun y hy => hs ▸ Submodule.subset_span hy
  have key : ∀ y ∈ N, ∃ z ∈ Submodule.span k (s : Set V), y - z ∈ sh 1 N := by
    intro y hy
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact ⟨y, Submodule.subset_span hy, by simp⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨z, hz, h⟩ := hy
      obtain ⟨z', hz', h'⟩ := hy'
      refine ⟨z + z', Submodule.add_mem _ hz hz', ?_⟩
      have := Submodule.add_mem _ h h'
      rwa [sub_add_sub_comm] at this
    | smul a y _ hy =>
      obtain ⟨z, hz, h⟩ := hy
      refine ⟨PowerSeries.constantCoeff a • z, Submodule.smul_mem _ _ hz, ?_⟩
      set t : k⟦X⟧ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) a
      have ha : a = PowerSeries.X * t + algebraMap k k⟦X⟧ (PowerSeries.constantCoeff a) :=
        PowerSeries.eq_X_mul_shift_add_const a
      have h3 : vv k ^ (1 : ℤ) • (t • z) ∈ sh 1 N := mem_sh_iff_exists.2 ⟨_, N.smul_mem t (hle hz), rfl⟩
      have h4 : vv k ^ (1 : ℤ) • (t • z) = (PowerSeries.X * t : k⟦X⟧) • z := by
        rw [zpow_one, mul_smul, vv_eq_coe_X]
        exact algebraMap_smul k⸨X⸩ (PowerSeries.X : k⟦X⟧) (t • z)
      have h5 : a • y - PowerSeries.constantCoeff a • z = a • (y - z) + (PowerSeries.X * t : k⟦X⟧) • z := by
        rw [← algebraMap_smul k⟦X⟧ (PowerSeries.constantCoeff a) z, eq_sub_of_add_eq ha.symm, smul_sub, sub_smul]
        abel
      rw [h5]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h) (h4 ▸ h3)
  haveI : FiniteDimensional k (Submodule.span k (s : Set V)) := FiniteDimensional.span_finset k s
  refine Module.Finite.of_surjective (Submodule.mkQ _ ∘ₗ Submodule.inclusion hle) fun w => ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨z, hz, h⟩ := key y hy
  refine ⟨⟨z, hz⟩, ?_⟩
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [eq_comm, Submodule.Quotient.eq]
  exact h

end

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W] [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W] [FiniteDimensional k⸨X⸩ W] {U : Type} [AddCommGroup U] [Module k⸨X⸩ U] [Module k⟦X⟧ U] [Module k U] [IsScalarTower k⟦X⟧ k⸨X⸩ U] [IsScalarTower k k⸨X⸩ U] [IsScalarTower k k⟦X⟧ U] [FiniteDimensional k⸨X⸩ U] (gV : V →ₗ[k] V) (gW : W →ₗ[k] W) (gU : U →ₗ[k] U) (f : W →ₗ[k⸨X⸩] V) (p : V →ₗ[k⸨X⸩] U), Semi R.γ gV → Function.Injective f → Function.Surjective p → Function.Exact f p → (∀ x, f (gW x) = gV (f x)) → (∀ x, p (gV x) = gU (p x)) → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC gV N → ∀ x : k, sen gV N x = sen gW (N.comap (f.restrictScalars k⟦X⟧)) x + sen gU (N.map (p.restrictScalars k⟦X⟧)) x := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ U _ _ _ _ _ _ _ _ gV gW gU f p hg _ _ hex hf hp N hN hC x
  have hN1 := (condC_iff_nab_mem gV N).1 hC
  have hN2 := nab_mem_sh_one R gV hg N hC
  have nf : ∀ y, f (nab gW y) = nab gV (f y) := fun y => by
    rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, hf]
  have np : ∀ y, p (nab gV y) = nab gU (p y) := fun y => by
    rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, hp]
  set N' := N.map (p.restrictScalars k⟦X⟧) with hN'
  have hsh : ∀ u, u ∈ sh 1 N' ↔ ∃ y ∈ sh 1 N, p y = u := by
    intro u
    constructor
    · intro hu
      obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := mem_sh_iff_exists.1 hu
      exact ⟨_, mem_sh_iff_exists.2 ⟨z, hz, rfl⟩, map_smul p _ _⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := mem_sh_iff_exists.1 hy
      exact mem_sh_iff_exists.2 ⟨p z, ⟨z, hz, rfl⟩, (map_smul p _ _).symm⟩
  have hU : ∀ u ∈ sh 1 N', nab gU u ∈ sh 1 N' := by
    intro u hu
    obtain ⟨y, hy, rfl⟩ := (hsh u).1 hu
    exact (hsh _).2 ⟨_, hN2 y hy, np y⟩
  let Q : Submodule k V := N.restrictScalars k ⊓ ((sh 1 N').restrictScalars k).comap (p.restrictScalars k)
  have hQ : ∀ y, y ∈ Q ↔ y ∈ N ∧ p y ∈ sh 1 N' := fun _ => Iff.rfl
  have hadd := GlobalTheory.PhiGam.GmultAdd.main (nab gV) (N.restrictScalars k) Q ((sh 1 N).restrictScalars k)
    (fun y hy => (hQ y).2 ⟨sh_one_le N hy, (hsh _).2 ⟨y, hy, rfl⟩⟩) inf_le_left hN1
    (fun y hy => (hQ _).2 ⟨hN1 y hy.1, by rw [np]; exact hU _ hy.2⟩) hN2 (finite_quot N hN.1) x
  have e1 : gmult (nab gV) (N.restrictScalars k) Q x = sen gU N' x :=
    gmult_transport (nab gV) (nab gU) (p.restrictScalars k) np _ _ (N'.restrictScalars k)
      ((sh 1 N').restrictScalars k) hN1 inf_le_left hU
      (fun y hy => ⟨y, hy, rfl⟩) (fun y hy => ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩)
      (by rintro _ ⟨y, hy, rfl⟩; exact ⟨y, hy, by simp⟩) x
  have e2 : sen gW (N.comap (f.restrictScalars k⟦X⟧)) x = gmult (nab gV) Q ((sh 1 N).restrictScalars k) x := by
    refine gmult_transport (nab gW) (nab gV) (f.restrictScalars k) nf _ _ _ _ ?_ (sh_one_le _) hN2 ?_ ?_ ?_ x
    · intro y hy
      change f (nab gW y) ∈ N
      rw [nf]
      exact hN1 _ hy
    · intro y hy
      refine (hQ _).2 ⟨hy, ?_⟩
      change p (f y) ∈ _
      rw [hex.apply_apply_eq_zero]
      exact Submodule.zero_mem _
    · intro y _
      change f y ∈ sh 1 N ↔ y ∈ sh 1 _
      rw [mem_sh_iff_smul_mem, mem_sh_iff_smul_mem, ← map_smul]
      rfl
    · intro z hz
      obtain ⟨y, hy, hyz⟩ := (hsh _).1 hz.2
      obtain ⟨w, hw⟩ := (hex (z - y)).1 (by rw [map_sub, hyz]; exact sub_self _)
      refine ⟨w, ?_, ?_⟩
      · change f w ∈ N
        rw [hw]
        exact N.sub_mem hz.1 (sh_one_le N hy)
      · change z - f w ∈ sh 1 N
        rwa [hw, sub_sub_cancel]
  rw [e2, ← e1, add_comm]
  exact hadd

end GlobalTheory.PhiGam.SenAdd
