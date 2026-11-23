import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}

def SectionsHaveFiniteDimension (p : X ⟶ Sp K) (M : LB X) (r : ℕ) : Prop :=
  ∃ s : Fin r → M.Sec, ∀ t : M.Sec, ∃! a : Fin r → K, ∀ j, t.f j = ∑ i, constFn p _ (a i) * (s i).f j

def Vol (p : X ⟶ Sp K) (M : LB X) (g : ℕ) (δ : ℝ) : Prop :=
  ∃ h : ℕ → ℕ, (∀ e, SectionsHaveFiniteDimension p (lbPow M e) (h e)) ∧
    Filter.Tendsto (fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) Filter.atTop (nhds δ)

def VAmp (p : X ⟶ Sp K) (M : LB X) {σ : Type} (th : σ → M.Sec) : Prop :=
  (⨆ i, Out.nonzeroLocus (th i) = ⊤) ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (th i)) ∧
    ∃ r : σ → Γ(X, Out.nonzeroLocus (th i)),
      (∀ j k, resG X (inf_le_right : Out.nonzeroLocus (th i) ⊓ M.U k ≤ M.U k) ((th j).f k) =
        resG X (inf_le_left : Out.nonzeroLocus (th i) ⊓ M.U k ≤ Out.nonzeroLocus (th i)) (r j) *
          resG X (inf_le_right : Out.nonzeroLocus (th i) ⊓ M.U k ≤ M.U k) ((th i).f k)) ∧
      ∀ f : Γ(X, Out.nonzeroLocus (th i)), ∃ F : MvPolynomial σ K,
        f = MvPolynomial.eval₂ (RingHom.comp (p.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) r F

def MapDeg (ψ : X ⟶ Y) (D : ℕ) : Prop :=
  ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
    letI := (ψ.app U).hom.toAlgebra
    Module.rank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) = (D : Cardinal)

def TorsBasis (A : Over (Sp K)) [GrpObj A] (k : ℕ) {m : ℕ} (pt : Fin m → (Out.baseOver (Sp K) ⟶ A)) : Prop :=
  0 < k ∧ (∀ i, pt i ^ k = 1) ∧ ∀ y : Out.baseOver (Sp K) ⟶ A, y ^ k = 1 →
    ∃! c : Fin m → ZMod k, Out.linComb pt (fun i => (c i).val) = y

def ActsBy {A : Over (Sp K)} [GrpObj A] {k m : ℕ} (pt : Fin m → (Out.baseOver (Sp K) ⟶ A)) (f : A ⟶ A)
    (Mat : Matrix (Fin m) (Fin m) (ZMod k)) : Prop :=
  0 < k ∧ ∀ i, pt i ≫ f = Out.linComb pt (fun i' => (Mat i' i).val)

def FormIs (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A) : Prop :=
  IsMonHom s ∧ LBIso (abelian₂ P.A M) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ s] P.L)

def SymB {A : Over (Sp K)} [GrpObj A] (M : LB A.left) : Prop := LBIso M (M.pull (GrpObj.inv : A ⟶ A).left)

theorem SectionsHaveFiniteDimension.le {p : X ⟶ Sp K} {M : LB X} {r r' : ℕ} (h : SectionsHaveFiniteDimension p M r) (h' : SectionsHaveFiniteDimension p M r') : r ≤ r' := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s', hs'⟩ := h'
  have hc : ∀ (U : X.Opens) (a : K), constFn p U a = AbLaw.cst p U a := fun _ _ => rfl
  choose B hB hBu using fun i => hs' (s i)
  let t : (Fin r → K) → M.Sec := fun a => ⟨fun j => ∑ i, AbLaw.cst p _ (a i) * (s i).f j, fun j k => by
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, (s i).compat j k]
    erw [AbLaw.rs_cst, AbLaw.rs_cst]
    ring⟩
  have hinj : Function.Injective (Matrix.vecMulLinear (Matrix.of B)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h0 : ∀ j, (t a).f j = 0 := fun j => by
      change ∑ i, AbLaw.cst p _ (a i) * (s i).f j = 0
      have hB' : ∀ i, (s i).f j = ∑ k, AbLaw.cst p _ (B i k) * (s' k).f j := fun i => hB i j
      simp_rw [hB', Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [← Finset.sum_mul, ← map_sum]
      have : ∑ i, a i * B i k = 0 := congrFun ha k
      rw [this, map_zero, zero_mul]
    refine (hs (t a)).unique (fun j => rfl) fun j => ?_
    rw [h0]
    simp [hc]
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

theorem SectionsHaveFiniteDimension.unique {p : X ⟶ Sp K} {M : LB X} {r r' : ℕ} (h : SectionsHaveFiniteDimension p M r) (h' : SectionsHaveFiniteDimension p M r') : r = r' :=
  le_antisymm (h.le h') (h'.le h)

theorem Vol.unique {p : X ⟶ Sp K} {M : LB X} {g : ℕ} {δ δ' : ℝ} (h : Vol p M g δ) (h' : Vol p M g δ') : δ = δ' := by
  obtain ⟨a, ha, ta⟩ := h
  obtain ⟨b, hb, tb⟩ := h'
  obtain rfl : a = b := funext fun e => (ha e).unique (hb e)
  exact tendsto_nhds_unique ta tb

theorem SectionsHaveFiniteDimension.one_of_isIso (p : X ⟶ Sp K) [IsIso p] {M : LB X} [Unique M.ι] (hU : M.U default = ⊤)
    (hg : ∀ i j, M.g i j = 1) : SectionsHaveFiniteDimension p M 1 := by
  have hb := AbLaw.cst_bijective p hU
  refine ⟨fun _ => ⟨fun _ => 1, fun i j => by rw [hg, map_one, map_one, Units.val_one, _root_.mul_one]⟩, fun t => ?_⟩
  obtain ⟨a, ha⟩ := hb.2 (t.f default)
  refine ⟨fun _ => a, fun j => ?_, fun b hb' => ?_⟩
  · obtain rfl : j = default := Subsingleton.elim _ _
    rw [Fin.sum_univ_one, _root_.mul_one]
    exact ha.symm
  · funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have := hb' default
    rw [Fin.sum_univ_one, _root_.mul_one] at this
    exact hb.1 (this.symm.trans ha.symm)

theorem SectionsHaveFiniteDimension.trivial_point (K : Type) [Field K] : SectionsHaveFiniteDimension (𝟙 (Sp K)) (Out.Inh.trivLB (Sp K)) 1 :=
  haveI : Unique (Out.Inh.trivLB (Sp K)).ι := inferInstanceAs (Unique PUnit)
  SectionsHaveFiniteDimension.one_of_isIso _ rfl fun _ _ => rfl

theorem Vol.trivial_point (K : Type) [Field K] : Vol (𝟙 (Sp K)) (Out.Inh.trivLB (Sp K)) 0 1 := by
  refine ⟨fun _ => 1, fun e => ?_, by simp⟩
  haveI : Unique (lbPow (Out.Inh.trivLB (Sp K)) e).ι := inferInstanceAs (Unique (PUnit → PUnit))
  exact SectionsHaveFiniteDimension.one_of_isIso _ (top_unique fun _ _ => Set.mem_iInter.2 fun _ => trivial)
    fun i j => Out.Inh.linComb_triv_g _ _ i j

example : ¬ SectionsHaveFiniteDimension (𝟙 (Sp ℚ)) (Out.Inh.trivLB (Sp ℚ)) 2 := fun h =>
  absurd (h.unique (SectionsHaveFiniteDimension.trivial_point ℚ)) (by decide)

example : ¬ Vol (𝟙 (Sp ℚ)) (Out.Inh.trivLB (Sp ℚ)) 0 0 := fun h =>
  zero_ne_one (h.unique (Vol.trivial_point ℚ))

theorem vAmp_iff_veryAmpleBy (p : X ⟶ Sp K) (M : LB X) {m : ℕ} (s : Fin (m + 1) → M.Sec) :
    VAmp p M s ↔ AbLaw.VeryAmpleBy p M s :=
  and_congr Iff.rfl (forall_congr' fun _ => and_congr Iff.rfl (exists_congr fun _ =>
    and_congr Iff.rfl (forall_congr' fun _ => exists_congr fun _ => eq_comm)))

theorem VAmp.comp_surjective {p : X ⟶ Sp K} {M : LB X} {σ τ : Type} {th : σ → M.Sec} (h : VAmp p M th)
    {e : τ → σ} (he : Function.Surjective e) : VAmp p M (fun i => th (e i)) := by
  refine ⟨(he.iSup_comp fun i => Out.nonzeroLocus (th i)).trans h.1, fun i => ⟨(h.2 (e i)).1, ?_⟩⟩
  obtain ⟨r, hr, hF⟩ := (h.2 (e i)).2
  refine ⟨fun j => r (e j), fun j k => hr (e j) k, fun f => ?_⟩
  obtain ⟨F, rfl⟩ := hF f
  obtain ⟨G, rfl⟩ := MvPolynomial.rename_surjective e he F
  exact ⟨G, MvPolynomial.eval₂_rename _ _ _ _⟩

theorem vAmp_comp_equiv (p : X ⟶ Sp K) (M : LB X) {σ τ : Type} (th : σ → M.Sec) (e : τ ≃ σ) :
    VAmp p M (fun i => th (e i)) ↔ VAmp p M th :=
  ⟨fun h => by simpa only [Equiv.apply_symm_apply] using h.comp_surjective e.symm.surjective,
    fun h => h.comp_surjective e.surjective⟩

theorem vAmp_iff_veryAmpleBy_equiv (p : X ⟶ Sp K) (M : LB X) {σ : Type} (th : σ → M.Sec) {m : ℕ}
    (e : Fin (m + 1) ≃ σ) : VAmp p M th ↔ AbLaw.VeryAmpleBy p M (fun i => th (e i)) :=
  (vAmp_comp_equiv p M th e).symm.trans (vAmp_iff_veryAmpleBy p M _)

theorem VAmp.exists_veryAmpleBy {p : X ⟶ Sp K} {M : LB X} {σ : Type} [Finite σ] [Nonempty σ] {th : σ → M.Sec}
    (h : VAmp p M th) : ∃ (m : ℕ) (e : Fin (m + 1) ≃ σ), AbLaw.VeryAmpleBy p M (fun i => th (e i)) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun hn => (hn ▸ e (Classical.arbitrary σ) : Fin 0).elim0
  exact ⟨m, e.symm, (vAmp_iff_veryAmpleBy_equiv p M th e.symm).1 h⟩

theorem VAmp.trivial_point (K : Type) [Field K] :
    VAmp (𝟙 (Sp K)) (Out.Inh.trivLB (Sp K)) (fun _ : Fin 1 => AbLaw.oneSec (Sp K)) :=
  (vAmp_iff_veryAmpleBy _ _ (m := 0) _).2 (AbLaw.veryAmpleBy_oneSec _)

example (p : X ⟶ Sp K) [Nonempty X] (M : LB X) (th : Empty → M.Sec) : ¬ VAmp p M th := fun h => by
  have hx : Classical.arbitrary X ∈ ⨆ i, Out.nonzeroLocus (th i) := by rw [h.1]; trivial
  obtain ⟨i, -⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact i.elim

theorem MapDeg.finrank_eq {ψ : X ⟶ Y} {D : ℕ} (h : MapDeg ψ D) (U : Y.Opens) (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) :
    letI := (ψ.app U).hom.toAlgebra
    Module.finrank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) = D :=
  (congrArg Cardinal.toNat (h U hU hne)).trans (Cardinal.toNat_natCast D)

theorem MapDeg.of_isFinite {ψ : X ⟶ Y} [IsFinite ψ] {D : ℕ}
    (h : ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
      letI := (ψ.app U).hom.toAlgebra
      Module.finrank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) = D) : MapDeg ψ D := fun U hU hne => by
  letI := (ψ.app U).hom.toAlgebra
  haveI : Nonempty U := hne.to_subtype
  haveI : Module.Finite Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) := ψ.finite_app U hU
  exact (Module.finrank_eq_rank _ _).symm.trans (congrArg _ (h U hU hne))

theorem MapDeg.unique [Nonempty Y] {ψ : X ⟶ Y} {D D' : ℕ} (h : MapDeg ψ D) (h' : MapDeg ψ D') : D = D' := by
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  exact (h.finrank_eq U hU ⟨y, hy⟩).symm.trans (h'.finrank_eq U hU ⟨y, hy⟩)

theorem MapDeg.id_one (X : Scheme.{0}) : MapDeg (𝟙 X) 1 := fun U _ hne =>
  haveI : Nonempty U := hne.to_subtype
  (Module.rank_self Γ(X, U)).trans Nat.cast_one.symm

section Torsion
variable {A : Over (Sp K)} [GrpObj A] {k m : ℕ} {pt : Fin m → (Out.baseOver (Sp K) ⟶ A)}

theorem TorsBasis.pos (h : TorsBasis A k pt) : 0 < k := h.1

theorem TorsBasis.pow_eq_one (h : TorsBasis A k pt) (i : Fin m) : pt i ^ k = 1 := h.2.1 i

theorem TorsBasis.existsUnique (h : TorsBasis A k pt) {y : Out.baseOver (Sp K) ⟶ A} (hy : y ^ k = 1) :
    ∃! c : Fin m → ZMod k, Out.linComb pt (fun i => (c i).val) = y := h.2.2 y hy

theorem ActsBy.pos {f : A ⟶ A} {Mat : Matrix (Fin m) (Fin m) (ZMod k)} (h : ActsBy pt f Mat) : 0 < k := h.1

theorem ActsBy.comp_eq {f : A ⟶ A} {Mat : Matrix (Fin m) (Fin m) (ZMod k)} (h : ActsBy pt f Mat) (i : Fin m) :
    pt i ≫ f = Out.linComb pt (fun i' => (Mat i' i).val) := h.2 i

theorem ActsBy.id_one [IsCommMonObj A] (hk : 0 < k) (hp : ∀ i, pt i ^ k = 1) :
    ActsBy pt (𝟙 A) (1 : Matrix (Fin m) (Fin m) (ZMod k)) := by
  refine ⟨hk, fun i => ?_⟩
  rw [Category.comp_id, Out.linComb, List.prod_ofFn, Finset.prod_eq_single i (fun b _ hb => by
    rw [Matrix.one_apply_ne hb, ZMod.val_zero, pow_zero]) (fun h => absurd (Finset.mem_univ _) h),
    Matrix.one_apply_eq, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ (hp i), pow_one]

theorem ActsBy.comp [IsCommMonObj A] (hp : ∀ i, pt i ^ k = 1) {f g : A ⟶ A} [IsMonHom g]
    {F G : Matrix (Fin m) (Fin m) (ZMod k)} (hf : ActsBy pt f F) (hg : ActsBy pt g G) :
    ActsBy pt (f ≫ g) (G * F) := by
  refine ⟨hf.pos, fun i => ?_⟩
  haveI : NeZero k := ⟨hf.pos.ne'⟩
  have hl : ∀ a : Fin m → ℕ, Out.linComb pt a = ∏ j, pt j ^ a j := fun a => List.prod_ofFn
  let φ : (Out.baseOver (Sp K) ⟶ A) →* (Out.baseOver (Sp K) ⟶ A) :=
    { toFun := (· ≫ g), map_one' := MonObj.one_comp _, map_mul' := fun a b => MonObj.mul_comp a b g }
  have hg' : ∀ j, φ (pt j) = ∏ l, pt l ^ (G l j).val := fun j => (hg.comp_eq j).trans (hl _)
  rw [← Category.assoc, hf.comp_eq i, hl, hl]
  change φ _ = _
  simp_rw [map_prod, map_pow, hg', ← Finset.prod_pow, ← pow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Finset.prod_pow_eq_pow_sum, pow_eq_pow_mod _ (hp l), Matrix.mul_apply, ← ZMod.val_natCast]
  simp

example (f : A ⟶ A) (Mat : Matrix (Fin m) (Fin m) (ZMod 0)) : ¬ ActsBy pt f Mat := fun h => lt_irrefl _ h.pos

end Torsion

theorem TorsBasis.of_level [IsAlgClosed K] (P : Out.PolAV (Sp K)) {k : ℕ} (hk : 0 < k) {ze : Γ(Sp K, ⊤)ˣ}
    (lev : Out.Level P k ze) : TorsBasis P.A k lev.pt := by
  haveI : NeZero k := ⟨hk.ne'⟩
  have e : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := by
    ext; rfl
  refine ⟨hk, lev.torsion, fun y hy => ?_⟩
  obtain ⟨c, hc⟩ := lev.span K (𝟙 _) y hy
  have hi := lev.indep K (𝟙 _)
  simp only [e, Category.id_comp] at hc hi
  refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, fun d hd => ?_⟩
  · simpa only [ZMod.val_cast_of_lt (c _).2] using hc
  · have := hi (fun i => ⟨(d i).val, ZMod.val_lt _⟩) c (hd.trans hc.symm)
    funext i
    rw [← this]
    simp

theorem FormIs.isMonHom {P : Out.PolAV (Sp K)} {M : LB P.A.left} {s : P.A ⟶ P.A} (h : FormIs P M s) :
    IsMonHom s := h.1

end GlobalTheory.ZV
end
