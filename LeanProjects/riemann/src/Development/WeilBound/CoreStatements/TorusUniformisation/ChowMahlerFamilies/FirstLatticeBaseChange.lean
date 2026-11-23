import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemSpanOverOfMem
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XDotdualBc
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSummandBc
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSummandOfQuot
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XGraphRestrictBc
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.GoodLatticeBaseChange

open PositivityTheory.Xgn.A_graph_restrict_bc PositivityTheory.Xgn.A_summand_of_quot

section One

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)

theorem locFree_retract {V W : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup W] [Module Ω W]
    {N r : ℕ} {L : AddSubgroup V} {A : AddSubgroup W} (hL : LocFree R N L)
    (hA : ∀ a ∈ R, ∀ e ∈ A, a • e ∈ A) (hr : Module.finrank Ω W = r)
    (j : W →ₗ[Ω] V) (π : V →ₗ[Ω] W) (h1 : ∀ w, π (j w) = w) (h2 : ∀ w ∈ A, j w ∈ L)
    (h3 : ∀ v ∈ L, π v ∈ A) : LocFree R r A := by
  obtain ⟨-, k, φ, v, hvL, hφ, hv⟩ := exists_dual R hL
  refine locFree_of_dual R hA hr (fun i => φ i ∘ₗ j) (fun i => π (v i)) (fun i => h3 _ (hvL i))
    (fun i e he => hφ i _ (h2 e he)) fun e => ?_
  have := congrArg π (hv (j e))
  rw [h1] at this
  simpa using this

theorem mem_stdLat {ι : Type} (v : ι → Ω) : v ∈ stdLat R ι ↔ ∀ i, v i ∈ R := by
  simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, forall_true_left]
  rfl

variable {F : Type} [Zero F] {n : ℕ}

theorem mem_vanSub (i : ℕ) (g : (Fin n → F) → Ω) :
    g ∈ vanSub Ω F n i ↔ ∀ x : Fin n → F, (∀ j : Fin n, i ≤ (j : ℕ) → x j = 0) → g x = 0 := by
  simp [vanSub, Submodule.mem_pi]

theorem linMap_apply (χ : F → Ω) (l : Fin n → Ω) (x : Fin n → F) :
    linMap n χ l x = ∑ i, l i * χ (x i) := by
  simp [linMap, Fintype.linearCombination_apply, Finset.sum_apply]

theorem linMap_single [One F] (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) (l : Fin n → Ω) (j : Fin n) :
    linMap n χ l (Pi.single j 1) = l j := by
  rw [linMap_apply, Finset.sum_eq_single j]
  · simp [h1]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb, h0]
  · simp

variable {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (p : ℕ)

theorem mem_af (χ : F → Ω) (l : Fin n → Ω) : l ∈ D.af R p χ ↔ linMap n χ l ∈ D.l1 R p := Iff.rfl

theorem mem_xId (χ : F → Ω) (i : Fin n) (c : Ω) : c ∈ D.xId χ i ↔
    ∃ m ∈ D.M, ∃ v ∈ vanSub Ω F n ((i : ℕ) + 1), m + v = c • fun x => χ (x i) := by
  simp only [LieLatticeData.xId, AddSubgroup.mem_comap, AddSubgroup.mem_sup]
  rfl

theorem af_retract [One F] (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1)
    (hS : Summand (D.l1 R p) (LinearMap.range (linMap n χ))) :
    ∃ π : ((Fin n → F) → Ω) →ₗ[Ω] (Fin n → Ω), (∀ w, π (linMap n χ w) = w) ∧
      ∀ v ∈ D.l1 R p, π v ∈ D.af R p χ := by
  obtain ⟨ρ, a1, a2, a3⟩ := hS
  let ev : ((Fin n → F) → Ω) →ₗ[Ω] (Fin n → Ω) :=
    LinearMap.pi fun j => LinearMap.proj (Pi.single j (1 : F) : Fin n → F)
  have hev : ∀ w, ev (linMap n χ w) = w := fun w => by
    funext j
    exact linMap_single χ h0 h1 w j
  refine ⟨ev ∘ₗ ρ, fun w => ?_, fun v hv => ?_⟩
  · rw [LinearMap.comp_apply, a2 _ ⟨w, rfl⟩, hev]
  · obtain ⟨w, hw⟩ := a1 v
    rw [mem_af, LinearMap.comp_apply, ← hw, hev, hw]
    exact a3 v hv

theorem xId_retract [One F] (χ : F → Ω) (h1 : χ 1 = 1) (i : Fin n)
    (hV : Summand D.M (vanSub Ω F n ((i : ℕ) + 1))) (hC : Summand D.M (charSub χ i)) :
    ∃ (j : Ω →ₗ[Ω] ((Fin n → F) → Ω)) (π : ((Fin n → F) → Ω) →ₗ[Ω] Ω), (∀ c, π (j c) = c) ∧
      (∀ c ∈ D.xId χ i, j c ∈ D.M) ∧ (∀ v ∈ D.M, π v ∈ D.xId χ i) ∧
      (∀ v ∈ vanSub Ω F n ((i : ℕ) + 1), π v = 0) ∧ π (fun x => χ (x i)) = 1 := by
  obtain ⟨ρ, a1, a2, a3⟩ := hV
  obtain ⟨σ, b1, b2, b3⟩ := hC
  let e : (Fin n → F) → Ω := fun x => χ (x i)
  let pt : Fin n → F := Pi.single i 1
  have hpt : ∀ v ∈ vanSub Ω F n ((i : ℕ) + 1), v pt = 0 := fun v hv =>
    (mem_vanSub _ v).1 hv pt fun j hj => Pi.single_eq_of_ne (fun h => by subst h; omega) _
  have he : e pt = 1 := by simp [e, pt, h1]
  have hle : ∀ v ∈ vanSub Ω F n ((i : ℕ) + 1), v ∈ charSub χ i := fun v hv =>
    Submodule.mem_sup_left hv
  have hec : e ∈ charSub χ i := Submodule.mem_sup_right (Submodule.subset_span rfl)
  let π : ((Fin n → F) → Ω) →ₗ[Ω] Ω := LinearMap.proj pt ∘ₗ σ
  have hπ : ∀ v, π v = σ v pt := fun _ => rfl
  have hπ0 : ∀ v ∈ vanSub Ω F n ((i : ℕ) + 1), π v = 0 := fun v hv => by
    rw [hπ, b2 v (hle v hv), hpt v hv]
  have hπ1 : π e = 1 := by rw [hπ, b2 e hec, he]
  refine ⟨(LinearMap.id - ρ) ∘ₗ LinearMap.toSpanSingleton Ω _ e, π, fun c => ?_, fun c hc => ?_,
    fun v hv => ?_, hπ0, hπ1⟩
  · show π (c • e - ρ (c • e)) = c
    rw [map_sub, hπ0 _ (a1 _), map_smul, hπ1, sub_zero, smul_eq_mul, mul_one]
  · obtain ⟨m, hm, v, hv, h⟩ := (mem_xId D χ i c).1 hc
    show c • e - ρ (c • e) ∈ D.M
    have h' : c • e = m + v := h.symm
    rw [h', map_add, a2 v hv, add_sub_add_right_eq_sub]
    exact D.M.sub_mem hm (a3 m hm)
  · obtain ⟨y, hy, z, hz, h⟩ := Submodule.mem_sup.1 (b1 v)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have hc : π v = c := by
      rw [hπ, ← h]
      show y pt + c * e pt = c
      rw [hpt y hy, he, zero_add, mul_one]
    rw [hc, mem_xId]
    exact ⟨σ v, b3 v hv, -y, Submodule.neg_mem _ hy, by rw [← h]; abel⟩

end One

section Two

variable {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C]
  (R : Subalgebra o Ω) (RC : Subalgebra o C)

theorem bc_apply {ι : Type} (v : ι → Ω) (i : ι) : bcMap Ω C ι v i = algebraMap Ω C (v i) := rfl

theorem isBC (ι : Type) [Finite ι] : IsBaseChange C (bcMap Ω C ι) :=
  IsBaseChange.finitePow ι (IsBaseChange.linearMap Ω C)

theorem eq_sum {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → C) (c : Ω) :
    algebraMap Ω C c • g = ∑ x, g x • bcMap Ω C ι (c • Pi.single x 1) := by
  funext y
  simp only [Finset.sum_apply, Pi.smul_apply, bc_apply, smul_eq_mul]
  rw [Finset.sum_eq_single y]
  · simp [mul_comm]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb.symm]
  · simp

variable {F : Type} [Zero F] [Fintype F] {n : ℕ}

theorem vanSub_bc (i : ℕ) :
    vanSub C F n i = Submodule.span C (bcMap Ω C _ '' vanSub Ω F n i) := by
  classical
  apply le_antisymm
  · intro g hg
    have h := eq_sum g (1 : Ω)
    rw [map_one, one_smul] at h
    rw [h]
    refine Submodule.sum_mem _ fun x _ => ?_
    by_cases hx : g x = 0
    · rw [hx, zero_smul]; exact Submodule.zero_mem _
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
      refine (mem_vanSub _ _).2 fun y hy => ?_
      have : y ≠ x := fun h => hx ((mem_vanSub _ _).1 hg x (h ▸ hy))
      simp [Pi.single_eq_of_ne this]
  · rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    refine (mem_vanSub _ _).2 fun y hy => ?_
    rw [bc_apply, (mem_vanSub _ _).1 hg y hy, map_zero]

theorem charSub_bc (χ : F → Ω) (i : Fin n) :
    charSub (fun a => algebraMap Ω C (χ a)) i = Submodule.span C (bcMap Ω C _ '' charSub χ i) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [vanSub_bc (Ω := Ω)]
      exact Submodule.span_mono (Set.image_mono fun v hv => Submodule.mem_sup_left hv)
    · refine Submodule.span_mono ?_
      rintro _ rfl
      exact ⟨fun x => χ (x i), Submodule.mem_sup_right (Submodule.subset_span rfl), rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hg
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [map_add, map_smul, ← algebraMap_smul C c]
    refine Submodule.add_mem_sup ?_ (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
    rw [vanSub_bc (Ω := Ω)]
    exact Submodule.subset_span ⟨y, hy, rfl⟩

omit [Zero F] [Fintype F] in
theorem linMap_bc (χ : F → Ω) (l : Fin n → Ω) :
    linMap n (fun a => algebraMap Ω C (χ a)) (bcMap Ω C _ l) = bcMap Ω C _ (linMap n χ l) := by
  funext x
  simp [linMap, Fintype.linearCombination_apply, Finset.sum_apply, bc_apply, Algebra.smul_def]

omit [Zero F] [Fintype F] in
theorem range_bc (χ : F → Ω) :
    LinearMap.range (linMap n (fun a => algebraMap Ω C (χ a))) =
      Submodule.span C (bcMap Ω C _ '' LinearMap.range (linMap n χ)) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    have h := eq_sum g (1 : Ω)
    rw [map_one, one_smul] at h
    rw [h, map_sum]
    refine Submodule.sum_mem _ fun x _ => ?_
    rw [map_smul, linMap_bc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨_, linMap_bc χ g⟩

variable {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (p : ℕ)

omit [Zero F] in
theorem first_lattice_base_change (hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC) :
    (D.bc RC).l1 RC p = spanOver RC (bcMap Ω C _ '' D.l1 R p) := by
  classical
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro x hx
      refine map_mem LinearMap.id ?_ hx
      rintro _ ⟨v, hv, rfl⟩
      exact mem_span ⟨v, AddSubgroup.mem_sup_left hv, rfl⟩
    · rintro _ ⟨g, hg, rfl⟩
      have h := eq_sum g (p : Ω)
      rw [map_natCast] at h
      show (p : C) • g ∈ _
      rw [h]
      refine AddSubgroup.sum_mem _ fun x _ => smul_mem ((mem_stdLat RC g).1 hg x)
        (mem_span ⟨_, AddSubgroup.mem_sup_right ⟨Pi.single x 1, ?_, rfl⟩, rfl⟩)
      refine (mem_stdLat R _).2 fun y => ?_
      rw [Pi.single_apply]
      split_ifs
      · exact R.one_mem
      · exact R.zero_mem
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, _, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨y, hy, _, ⟨z, hz, rfl⟩, rfl⟩ := AddSubgroup.mem_sup.1 hv
    rw [map_add, smul_add]
    refine AddSubgroup.add_mem_sup (smul_mem ha (mem_span ⟨y, hy, rfl⟩))
      ⟨a • bcMap Ω C _ z, (mem_stdLat RC _).2 fun x => ?_, ?_⟩
    · exact RC.mul_mem ha (hR _ ((mem_stdLat R z).1 hz x))
    · funext x
      show (p : C) * (a * algebraMap Ω C (z x)) = a * algebraMap Ω C ((p : Ω) * z x)
      rw [map_mul, map_natCast]; ring

theorem af_bc [One F] (hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC) (χ : F → Ω) (h0 : χ 0 = 0)
    (h1 : χ 1 = 1) (hS : Summand (D.l1 R p) (LinearMap.range (linMap n χ))) :
    (D.bc RC).af RC p (fun a => algebraMap Ω C (χ a)) = spanOver RC (bcMap Ω C _ '' D.af R p χ) := by
  obtain ⟨π, a1, a2⟩ := af_retract R D p χ h0 h1 hS
  obtain ⟨τ, hτ⟩ : ∃ τ : ((Fin n → F) → C) →ₗ[C] (Fin n → C),
      ∀ v, τ (bcMap Ω C _ v) = bcMap Ω C _ (π v) :=
    ⟨(isBC _).lift (bcMap Ω C _ ∘ₗ π), fun v => (isBC _).lift_eq _ v⟩
  ext w
  rw [mem_af, first_lattice_base_change R RC D p hR]
  constructor
  · intro hw
    have hid : τ (linMap n (fun a => algebraMap Ω C (χ a)) w) = w := by
      have h := eq_sum w (1 : Ω)
      rw [map_one, one_smul] at h
      rw [h, map_sum, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul, map_smul, linMap_bc, hτ, a1]
    rw [← hid]
    refine map_mem τ ?_ hw
    rintro _ ⟨v, hv, rfl⟩
    rw [hτ]
    exact mem_span ⟨_, a2 v hv, rfl⟩
  · intro hw
    refine map_mem _ ?_ hw
    rintro _ ⟨v, hv, rfl⟩
    rw [linMap_bc]
    exact mem_span ⟨_, hv, rfl⟩

theorem xId_bc [One F] (χ : F → Ω) (h1 : χ 1 = 1) (i : Fin n)
    (hV : Summand D.M (vanSub Ω F n ((i : ℕ) + 1))) (hC : Summand D.M (charSub χ i)) :
    (D.bc RC).xId (fun a => algebraMap Ω C (χ a)) i = spanOver RC (algebraMap Ω C '' D.xId χ i) := by
  obtain ⟨-, π, -, -, a1, a2, a3⟩ := xId_retract D χ h1 i hV hC
  obtain ⟨τ, hτ⟩ : ∃ τ : ((Fin n → F) → C) →ₗ[C] C,
      ∀ v, τ (bcMap Ω C _ v) = algebraMap Ω C (π v) :=
    ⟨(isBC _).lift (Algebra.linearMap Ω C ∘ₗ π), fun v => (isBC _).lift_eq _ v⟩
  apply le_antisymm
  · intro c hc
    obtain ⟨m, hm, v, hv, h⟩ := (mem_xId _ _ _ _).1 hc
    have h0 : τ v = 0 := by
      rw [vanSub_bc (Ω := Ω)] at hv
      refine (Submodule.span_le (p := LinearMap.ker τ)).2 ?_ hv
      rintro _ ⟨y, hy, rfl⟩
      show τ _ = 0
      rw [hτ, a2 y hy, map_zero]
    have h1 : τ (fun x => algebraMap Ω C (χ (x i))) = 1 := by
      have := hτ (fun x => χ (x i))
      rw [a3, map_one] at this
      exact this
    have h2 := congrArg τ h
    rw [map_add, h0, add_zero, map_smul, h1, smul_eq_mul, mul_one] at h2
    rw [← h2]
    refine map_mem τ ?_ hm
    rintro _ ⟨v, hv, rfl⟩
    rw [hτ]
    exact mem_span ⟨_, a1 v hv, rfl⟩
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, _, ⟨c, hc, rfl⟩, rfl⟩
    obtain ⟨m, hm, v, hv, h⟩ := (mem_xId _ _ _ _).1 hc
    refine (mem_xId _ _ _ _).2 ⟨a • bcMap Ω C _ m, smul_mem ha (mem_span ⟨m, hm, rfl⟩),
      a • bcMap Ω C _ v, Submodule.smul_mem _ _ ?_, ?_⟩
    · rw [vanSub_bc (Ω := Ω)]
      exact Submodule.subset_span ⟨v, hv, rfl⟩
    · rw [← smul_add, ← map_add, h]
      funext x
      show a * algebraMap Ω C (c * χ (x i)) = a * algebraMap Ω C c * algebraMap Ω C (χ (x i))
      rw [map_mul, mul_assoc]

end Two

end PositivityTheory.Xgn.GoodLatticeBaseChange

open PositivityTheory.Xgn.GoodLatticeBaseChange in
theorem PositivityTheory.Xgn.good_lattice_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, LocFree R n (D.af R p (χ τ)) ∧ LocFree R n (D.hh R p (χ τ)) ∧ D.af R p (χ τ) ≤ stdLat R _ ∧ ∀ i, LocFree R 1 (D.xId (χ τ) i)) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → (D.bc RC).Good₁ RC p (fun τ a => algebraMap Ω C (χ τ a)) ∧ ∀ τ, (D.bc RC).af RC p (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.af R p (χ τ)) ∧ (D.bc RC).hh RC p (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.hh R p (χ τ)) ∧ ∀ i, (D.bc RC).xId (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.xId (χ τ) i) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hχ hB hG
  obtain ⟨-, -, -, -, hχ⟩ := hχ
  have haf : ∀ τ, LocFree R n (D.af R p (χ τ)) := fun τ => by
    obtain ⟨π, a1, a2⟩ := af_retract R D p (χ τ) (hχ τ).1 (hχ τ).2.1 (hG.lin τ)
    refine locFree_retract R hG.l1 (fun a ha e he => ?_) (by simp) (linMap n (χ τ)) π a1
      (fun _ h => h) a2
    rw [mem_af, map_smul]
    exact hG.l1.1 a ha _ he
  refine ⟨fun τ => ⟨haf τ, ?_, ?_, fun i => ?_⟩, ?_⟩
  · exact (PositivityTheory.Xgn.t_dotdual_bc R R (fun _ h => h) n _ (haf τ)).1
  · intro l hl
    refine (mem_stdLat R l).2 fun j => ?_
    rw [← linMap_single (χ τ) (hχ τ).1 (hχ τ).2.1 l j]
    have hle : D.l1 R p ≤ stdLat R _ := by
      refine sup_le hB.M_le ?_
      rintro _ ⟨g, hg, rfl⟩
      exact (mem_stdLat R _).2 fun x => R.mul_mem (natCast_mem R p) ((mem_stdLat R g).1 hg x)
    exact (mem_stdLat R _).1 (hle hl) _
  · obtain ⟨j, π, a1, a2, a3, -, -⟩ := xId_retract D (χ τ) (hχ τ).2.1 i (hG.van _) (hG.char τ i)
    refine locFree_retract R hB.freeM (fun a ha e he => ?_) (by simp) j π a1 a2 a3
    obtain ⟨m, hm, v, hv, h⟩ := (mem_xId _ _ _ _).1 he
    exact (mem_xId _ _ _ _).2 ⟨a • m, hB.freeM.1 a ha m hm, a • v, Submodule.smul_mem _ _ hv,
      by rw [← smul_add, h, smul_smul, smul_eq_mul]⟩
  intro C _ _ _ _ RC hR
  refine ⟨⟨?_, fun τ => ?_, fun i => ?_, fun τ i => ?_⟩, fun τ => ?_⟩
  · rw [first_lattice_base_change R RC D p hR]
    exact LocFreeBC.locFree_baseChange R RC hR _ (isBC _) _ _ hG.l1
  · rw [first_lattice_base_change R RC D p hR, range_bc]
    exact (PositivityTheory.Xgn.t_summand_bc R RC hR _ (isBC _) _ _ hG.l1.1 (hG.lin τ)).1
  · rw [vanSub_bc (Ω := Ω)]
    exact (PositivityTheory.Xgn.t_summand_bc R RC hR _ (isBC _) _ _ hB.freeM.1 (hG.van i)).1
  · rw [charSub_bc]
    exact (PositivityTheory.Xgn.t_summand_bc R RC hR _ (isBC _) _ _ hB.freeM.1 (hG.char τ i)).1
  · have h := af_bc R RC D p hR (χ τ) (hχ τ).1 (hχ τ).2.1 (hG.lin τ)
    refine ⟨h, ?_, fun i => xId_bc RC D (χ τ) (hχ τ).2.1 i (hG.van _) (hG.char τ i)⟩
    unfold LieLatticeData.hh
    rw [h]
    exact (PositivityTheory.Xgn.t_dotdual_bc R RC hR n _ (haf τ)).2.2
