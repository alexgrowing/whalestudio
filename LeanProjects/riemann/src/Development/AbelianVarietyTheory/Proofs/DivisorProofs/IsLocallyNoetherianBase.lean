import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOfMaximal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSheafLocalModelBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSectionsFormFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.RangeJSubsetAbLocus

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
open GlobalTheory.GroupBplus (AffOp IsPropG TorsionMap Tors)
open GlobalTheory.RingChain (RChain IsOf)
open GlobalTheory.LineNorm (IsTanBasis)
open GlobalTheory.OmegaHT (crd ToOpen)
open GlobalTheory.PDivGroup (muRoot omegaMap tateMap dualHom dlog)
open GlobalTheory.PerfdLat (PrismData ConstTate eps dualBaseChange bcTate piMap)
open GlobalTheory.Published (CycPerfd)
open scoped TensorProduct Pointwise

namespace GlobalTheory.ChainPts.SysB

section Algebra

@[elab_as_elim]
theorem tmul_ind {R A M : Type} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M] {P : A ⊗[R] M → Prop}
    (h1 : ∀ s, P (1 ⊗ₜ s)) (hs : ∀ (a : A) x, P x → P (a • x)) (ha : ∀ x y, P x → P y → P (x + y)) (x : A ⊗[R] M) : P x := by
  induction x using TensorProduct.induction_on with
  | zero => simpa using hs 0 _ (h1 0)
  | tmul a s => simpa [TensorProduct.smul_tmul'] using hs a _ (h1 s)
  | add x y hx hy => exact ha x y hx hy

section Ext

variable {R A A' M N : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {L P : Type} [AddCommGroup L] [Module A' L] [AddCommGroup P] [Module A' P] {σ : A →+* A'}

theorem semi_ext {Q T : Type} [AddCommGroup Q] [Module A Q] [AddCommGroup T] [Module A' T] (m : A ⊗[R] M →ₛₗ[σ] L)
    (c' : L →ₗ[A'] P) (c : A ⊗[R] M →ₗ[A] Q) (u : Q →ₛₗ[σ] T) (v : T →ₗ[A'] P)
    (h : ∀ s, c' (m (1 ⊗ₜ s)) = v (u (c (1 ⊗ₜ s)))) (w : A ⊗[R] M) : c' (m w) = v (u (c w)) := by
  induction w using tmul_ind with
  | h1 s => exact h s
  | hs a w hw => simp only [map_smul, map_smulₛₗ, hw, RingHom.id_apply]
  | ha w w' hw hw' => simp only [map_add, hw, hw']

theorem pair_ext (pr : A ⊗[R] M →ₗ[A] Module.Dual A (A ⊗[R] N)) (pr' : L →ₗ[A'] Module.Dual A' P)
    (l : A ⊗[R] M →ₛₗ[σ] L) (m : A ⊗[R] N →ₛₗ[σ] P)
    (h : ∀ y w, pr' (l (1 ⊗ₜ y)) (m (1 ⊗ₜ w)) = σ (pr (1 ⊗ₜ y) (1 ⊗ₜ w))) (y : A ⊗[R] M) (w : A ⊗[R] N) :
    pr' (l y) (m w) = σ (pr y w) := by
  induction y using tmul_ind with
  | h1 y =>
    induction w using tmul_ind with
    | h1 w => exact h y w
    | hs a w hw => rw [m.map_smulₛₗ, map_smul, hw, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
    | ha w w' hw hw' => simp only [map_add, hw, hw']
  | hs a y hy =>
    rw [l.map_smulₛₗ, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hy, smul_eq_mul, smul_eq_mul, map_mul]
  | ha y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']

theorem adj_ext (pr : A ⊗[R] M →ₗ[A] Module.Dual A (A ⊗[R] N)) (l : M →ₗ[R] M) (m : N →ₗ[R] N)
    (h : ∀ y w, pr (1 ⊗ₜ l y) (1 ⊗ₜ w) = pr (1 ⊗ₜ y) (1 ⊗ₜ m w)) (y : A ⊗[R] M) (w : A ⊗[R] N) :
    pr (l.baseChange A y) w = pr y (m.baseChange A w) := by
  induction y using tmul_ind with
  | h1 y =>
    induction w using tmul_ind with
    | h1 w => exact h y w
    | hs a w hw => simp only [map_smul, hw]
    | ha w w' hw hw' => simp only [map_add, hw, hw']
  | hs a y hy => simp only [map_smul, LinearMap.smul_apply, hy]
  | ha y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']

theorem lin_ext {Q : Type} [AddCommGroup Q] [Module A Q] (c : A ⊗[R] M →ₗ[A] Q) (l : M →ₗ[R] M) (v : Q →ₗ[A] Q)
    (h : ∀ s, c (1 ⊗ₜ l s) = v (c (1 ⊗ₜ s))) (w : A ⊗[R] M) : c (l.baseChange A w) = v (c w) := by
  induction w using tmul_ind with
  | h1 s => exact h s
  | hs a w hw => simp only [map_smul, hw]
  | ha w w' hw hw' => simp only [map_add, hw, hw']

theorem coord_ext {ι : Type} (b : Module.Basis ι R M) (i : ι) (u : Module.Dual A (A ⊗[R] M))
    (h : ∀ s, u (1 ⊗ₜ s) = algebraMap R A (b.repr s i)) (w : A ⊗[R] M) : u w = (b.baseChange A).repr w i := by
  induction w using tmul_ind with
  | h1 s => rw [h, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  | hs a w hw => simp only [map_smul, hw, Finsupp.smul_apply]
  | ha w w' hw hw' => simp only [map_add, hw, hw', Finsupp.add_apply]

end Ext

variable {p n o : ℕ} {A : Type} [CommRing A] {π : A} {γ : ℕ → A} {Lie Om : Type} [AddCommGroup Lie] [Module A Lie]
  [AddCommGroup Om] [Module A Om] (C : RChain p A n o π γ Lie Om)

theorem rho_smul (w : Om) : C.ρ (π • w) = 0 := by
  obtain ⟨q, hq⟩ := Submodule.Quotient.mk_surjective _ (C.ρ w)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [map_smul, ← hq, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
    (Submodule.Quotient.mk_eq_zero (x := π • x) _).2 (Submodule.smul_mem_pointwise_smul x.1 π ⊤ trivial), Submodule.Quotient.mk_zero]

variable {K : Type} [NormedField K] [IsUltrametricDist K] (ψ : A →+* ↥(intO K)) {r : ℕ} (f : Module.Basis (Fin r) A Om)
  (a : Fin r → K)

def ev : Om →ₛₗ[(intO K).subtype.comp ψ] K where
  toFun w := ∑ l, (ψ (f.repr w l) : K) * a l
  map_add' w w' := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c w := by simp [Finset.mul_sum, mul_assoc]

theorem ev_basis (l : Fin r) : ev ψ f a (f l) = a l := by
  change ∑ m, (ψ (f.repr (f l) m) : K) * a m = a l
  rw [Finset.sum_eq_single l (fun m _ h => by simp [Finsupp.single_apply, h.symm]) (by simp)]
  simp

def evInt : Submodule A Om where
  carrier := {w | ev ψ f a w ∈ intO K}
  add_mem' hx hy := by simpa only [Set.mem_setOf_eq, map_add] using add_mem hx hy
  zero_mem' := by simpa only [Set.mem_setOf_eq, map_zero] using zero_mem _
  smul_mem' c w hw := by
    change ev ψ f a _ ∈ intO K
    rw [map_smulₛₗ]
    exact mul_mem (ψ c).2 hw

variable {η : Fin n → Om}

theorem ker_le_evInt (hR : ∀ w : Om, C.ρ w = 0 ↔ w ∈ Submodule.span A (Set.range η) ⊔ (p : A) • (⊤ : Submodule A Om))
    (h1 : ∀ j, ‖ev ψ f a (η j)‖ ≤ 1) (h2 : ∀ l, ‖(p : K) * a l‖ ≤ 1) {w : Om} (hw : C.ρ w = 0) : ev ψ f a w ∈ intO K := by
  refine (show _ ≤ evInt ψ f a from sup_le (Submodule.span_le.2 ?_) ?_) ((hR w).1 hw)
  · rintro _ ⟨j, rfl⟩
    exact h1 j
  · intro x hx
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [← f.sum_repr y, Finset.smul_sum]
    refine sum_mem fun l _ => ?_
    rw [smul_comm]
    refine Submodule.smul_mem _ _ ?_
    change ev ψ f a _ ∈ intO K
    rw [map_smulₛₗ, ev_basis, map_natCast]
    exact h2 l

theorem cut_iff_kerR (hR : ∀ w : Om, C.ρ w = 0 ↔ w ∈ Submodule.span A (Set.range η) ⊔ (p : A) • (⊤ : Submodule A Om))
    (hK : C.kerR ψ f = (Submodule.span ↥(intO K) {v : Fin r → ↥(intO K) | ∃ w, C.ρ w = 0 ∧ v = fun l => ψ (f.repr w l)} :
      Set (Fin r → ↥(intO K)))) :
    ((∀ j, ‖ev ψ f a (η j)‖ ≤ 1) ∧ ∀ l, ‖(p : K) * a l‖ ≤ 1) ↔ ∀ c ∈ C.kerR ψ f, ‖∑ l, (c l : K) * a l‖ ≤ 1 := by
  rw [hK]
  refine ⟨fun ⟨h1, h2⟩ c hc => ?_, fun h => ⟨fun j => h _ (Submodule.subset_span ⟨η j, (hR _).2
    (Submodule.mem_sup_left (Submodule.subset_span ⟨j, rfl⟩)), rfl⟩), fun l => ?_⟩⟩
  · change ∑ l, (c l : K) * a l ∈ intO K
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact ker_le_evInt C ψ f a hR h1 h2 hw
    | zero => simpa using zero_mem _
    | add x y _ _ hx hy => simpa [add_mul, Finset.sum_add_distrib] using add_mem hx hy
    | smul c x _ hx => simpa [Finset.mul_sum, mul_assoc] using mul_mem c.2 hx
  · have k := h _ (Submodule.subset_span ⟨(p : A) • f l, (hR _).2
      (Submodule.mem_sup_right (Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial)), rfl⟩)
    change ‖ev ψ f a _‖ ≤ 1 at k
    rwa [map_smulₛₗ, ev_basis, map_natCast] at k

theorem cut_iff_kerJ (hR : ∀ w : Om, C.ρ w = 0 ↔ w ∈ Submodule.span A (Set.range η) ⊔ (p : A) • (⊤ : Submodule A Om))
    (e : Fin r → Lie) (hJ : ∀ l (x : C.L 0), C.j (e l) = Submodule.Quotient.mk x → ∀ j, π ∣ x.1 j - f.repr (η j) l)
    (hπ : π ∣ (p : A)) (h0 : ψ π ≠ 0) :
    ((∀ j, ‖ev ψ f a (η j)‖ ≤ 1) ∧ ∀ l, ‖(p : K) * a l‖ ≤ 1) ↔ ∃ c ∈ C.kerJ ψ e, ∀ l, (c l : K) = (ψ π : K) * a l := by
  have key : ∀ (c : Fin r → ↥(intO K)) (x : Fin r → C.L 0), (∀ l, C.j (e l) = Submodule.Quotient.mk (x l)) →
      (∀ l, (c l : K) = (ψ π : K) * a l) → ∀ j, ∃ d : ↥(intO K),
        (((∑ l, c l • piMap ψ _ (x l).1) j : ↥(intO K)) : K) = (ψ π : K) * (ev ψ f a (η j) + d) := fun c x hx hc j => by
    choose d hd using fun l => hJ l _ (hx l) j
    refine ⟨∑ l, c l * ψ (d l), ?_⟩
    change _ = (ψ π : K) * (∑ l, (ψ (f.repr (η j) l) : K) * a l + _)
    simp only [Finset.sum_apply, Pi.smul_apply, GlobalTheory.PerfdLat.piMap_apply, sub_eq_iff_eq_add.1 (hd _), smul_eq_mul, map_add,
      map_mul]
    push_cast
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hc]; ring
  have h0' : (ψ π : K) ≠ 0 := fun h => h0 (Subtype.ext h)
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨c, ⟨x, hx, hc⟩, ha⟩ => ⟨fun j => ?_, fun l => ?_⟩⟩
  · have hc : ∀ l, (ψ π : K) * a l ∈ intO K := fun l => by
      have k := ker_le_evInt C ψ f a hR h1 h2 (rho_smul C (f l))
      rwa [map_smulₛₗ, ev_basis] at k
    choose x hx using fun l => Submodule.Quotient.mk_surjective _ (C.j (e l))
    refine ⟨fun l => ⟨_, hc l⟩, ⟨x, fun l => (hx l).symm, ?_⟩, fun _ => rfl⟩
    choose d hd using key (fun l => ⟨_, hc l⟩) x (fun l => (hx l).symm) fun _ => rfl
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
      ⟨fun j => ⟨_, h1 j⟩ + d j, trivial, funext fun j => Subtype.ext (hd j).symm⟩
  · obtain ⟨d, hd⟩ := key c x hx ha j
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hc
    rw [← hy] at hd
    have k : (y j : K) = ev ψ f a (η j) + d := mul_left_cancel₀ h0' hd
    change ev ψ f a (η j) ∈ intO K
    rw [← sub_eq_iff_eq_add.2 k]
    exact sub_mem (y j).2 d.2
  · obtain ⟨q, hq⟩ := hπ
    have k : (p : K) = (ψ q : K) * (ψ π : K) := by
      rw [mul_comm, ← Subring.coe_mul, ← map_mul, ← hq, map_natCast]; simp
    change _ ∈ intO K
    rw [k, mul_assoc, ← ha]
    exact mul_mem (ψ q).2 (c l).2

end Algebra

section Sec

variable {X : Scheme.{0}} [IsIntegral X]

theorem res_algebraMap {U U' : AffOp X} (hle : U'.1 ≤ U.1) (a : Γ(X, U.1)) :
    AffOp.res hle (algebraMap _ _ a) = algebraMap _ _ (resG X hle a) :=
  Subtype.ext (congrArg (algebraMap X.functionField (GlobalTheory.GroupBplus.Kbar X))
    (X.presheaf.germ_res_apply (homOfLE hle) _ _ a).symm)

theorem exists_res (F : X.Modules) {U U' : AffOp X} (hle : U'.1 ≤ U.1) :
    ∃ l : U.Bp ⊗[Γ(X, U.1)] Γ(F, U.1) →ₛₗ[AffOp.res hle] U'.Bp ⊗[Γ(X, U'.1)] Γ(F, U'.1),
      ∀ s, l (1 ⊗ₜ s) = 1 ⊗ₜ resM F hle s := by
  let f : U.Bp →ₛₗ[resG X hle] U'.Bp := ⟨(AffOp.res hle).toAddMonoidHom.toAddHom, fun a b => by
    change AffOp.res hle _ = _ • AffOp.res hle _
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, res_algebraMap]⟩
  let g : Γ(F, U.1) →ₛₗ[resG X hle] Γ(F, U'.1) := ⟨⟨resM F hle, fun _ _ => map_add _ _ _⟩, fun a s => GlobalTheory.Twist.resM_smul ..⟩
  refine ⟨⟨(TensorProduct.map f g).toAddHom, fun a x => ?_⟩, fun s => ?_⟩
  · change TensorProduct.map f g _ = _ • TensorProduct.map f g _
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b s =>
      rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.smul_tmul']
      exact congrArg (· ⊗ₜ _) (map_mul (AffOp.res hle) a b)
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  · exact (TensorProduct.map_tmul f g 1 s).trans (congrArg (· ⊗ₜ _) (map_one (AffOp.res hle)))

theorem valF_toX (U : AffOp X) {k : Type} [Field k] (κ : U.Bp →+* k) (g : Γ(X, ⊤)) :
    valF (spMap κ ≫ U.toX) ⊤ g = κ (algebraMap Γ(X, U.1) _ (resG X le_top g)) := by
  have e : spMap κ ≫ U.toX = spMap (κ.comp (algebraMap _ _)) ≫ U.2.1.fromSpec := by
    rw [GlobalTheory.Cris.spMap_comp, Category.assoc]; rfl
  have h : ⊤ ≤ (spMap (κ.comp (algebraMap _ _)) ≫ U.2.1.fromSpec) ⁻¹ᵁ U.1 := by
    rw [Scheme.Hom.comp_preimage, U.2.1.fromSpec_preimage_self]; exact le_rfl
  rw [e, ← GlobalTheory.FieldPtGlue.valF_restrict le_top h]
  exact GlobalTheory.ShFam.Pad.Pull.valF_fromSpec U.2.1 _ _

end Sec

section Main

open GlobalTheory.ChainPts.DualPres GlobalTheory.GroupBplus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : LocM.Mdl Y i₀} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {h : B.X ⟶ Z.X}
  {r : ℕ} {x : Fin r → Letter Dw} {Om : AM B (𝓞 E)} {s : ∀ a : Fin Z.m, Fin r → Γ(Om.V, h ⁻¹ᵁ (Z.U a).1)}

theorem isEqLat_dual (k : IsEqLat Z h x true Om s) :
    IsEqLat Z h x false (dualA H.bar Om) fun a => (k.2.2.1.frame a).coord :=
  ⟨isAdd_dualA _ k.1, k.2.1.dual, isLat_dual k.2.2.1 k.2.1, fun a i c => dualMap_coord_eig _ (k.2.2.1.frame a)
    (fun i => (h.app (Z.U a).1).hom (Z.alg a (embK Z.i.c (x i).1 c)))
    (fun i => (k.2.2.2 a i (H.bar c)).trans (by rw [if_pos rfl, bar_bar])) i⟩

theorem isEqLat_rev (k : IsEqLat Z h x true Om s) : IsEqLat Z h (fun i => x i.rev) true Om fun a i => s a i.rev :=
  ⟨k.1, k.2.1, isLat_perm k.2.2.1 Fin.revPerm, fun a _ c => k.2.2.2 a _ c⟩

theorem charZero_kbar {X : Scheme.{0}} [IsIntegral X] {h : X ⟶ Z.X} (ho : ToOpen Z h) : CharZero (Kbar X) := by
  have h1 : h (genericPoint X) ∈ ⋃ a, ((Z.U a).1 : Set Z.X) := by
    rw [Z.cover]
    exact ho _ fun y hy => (hy.antisymm (genericPoint_specializes y)).eq
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 h1
  exact charZero_of_injective_ringHom (f := (algebraMap X.functionField (Kbar X)).comp
    ((X.presheaf.germ _ (genericPoint X) ha).hom.comp ((h.app (Z.U a).1).hom.comp (Z.alg a)))) (RingHom.injective _)

variable [Fact p.Prime]

theorem mem_lat_iff (hT : TanSt) (hH : HTSt) [IsLocallyNoetherian (Y Z.i).X] (hx : Function.Bijective x)
    (hs : ∀ a, GlobalTheory.VB.IsFrame (s a)) (U : AffOp B.X) {t : SAB H (Sp U.Bp)} {φt : t.G.left ⟶ (Y Z.i).t.G.left}
    (hφt : IsGrpPullback t.G (Y Z.i).t.G (U.toX ≫ h ≫ Z.π) φt) {lam : SecBp Om.V U →ₗ[U.Bp] Pdiv.omega t.G}
    (hb : Function.Bijective lam) (hl : FormLink Z h x hs U φt lam) {GG : PDivGroup p U.Bp}
    {act : PDivGroup.Action (𝓞 E) GG} {pol : GG ≅ GG.dual} {θ : TorsionMap t.G GG} {ε : (PDivGroup.mu p U.Bp).Tate}
    {τ : Dw.La →+ GG.Tate} (hP : IsPropG Dw t GG act pol θ ε τ) {n : ℕ} (e : GG.height = n)
    (b : Module.Basis (Fin n) ℤ Dw.La) {c : Pdiv.omega t.G →ₗ[U.Bp] GG.omega} (hc : θ.IsOmega c) {η : Fin n → SecBp Om.V U}
    (hη : IsDlog (ct hP e b) e (c ∘ₗ lam) η) {f : Fin r → Γ(Om.V, U.1)} (hf : GlobalTheory.VB.IsFrame f)
    (fb : Module.Basis (Fin r) U.Bp (SecBp Om.V U)) (hfb : ∀ l, fb l = 1 ⊗ₜ f l) (y : Z.Pt)
    (ψ : U.Bp →+* ↥(intO ↥y.C.S)) (hψ : (spMap ψ ≫ U.toX) ≫ h = y.z) (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S)
    (hφ : spMap φ ≫ Z.chart a = y.gen) (cf : Fin r → ↥y.C.S) (v : Sp (DualNumber ↥y.C.S) ⟶ (Y Z.i).t.G.left)
    (hv : IsCombAtG (Y Z.i).t (y.gen ≫ Z.π) (fun i => (Z.fr a).bc φ (x i).1 (x i).2) cf v) (A : Fin r → ↥y.C.S)
    (hA : ∀ l, A l = ∑ i, cf i * valF (spMap (intO ↥y.C.S).subtype ≫ spMap ψ ≫ U.toX) _ (coef true hf (hs a) l i)) :
    v ∈ lat (Y Z.i).t p (y.gen ≫ Z.π) true ↔ (∀ j, ‖ev ψ fb A (η j)‖ ≤ 1) ∧ ∀ l, ‖(p : ↥y.C.S) * A l‖ ≤ 1 := by
  obtain ⟨u, hu, hd, hco⟩ := hT E H Dw Xo p W Y i₀ Z B.X h r x hx Om.V s hs U t φt hφt lam hb hl f hf
  have e0 : spMap ((intO ↥y.C.S).subtype.comp ψ) ≫ U.toX = spMap (intO ↥y.C.S).subtype ≫ spMap ψ ≫ U.toX := by
    rw [GlobalTheory.Cris.spMap_comp, Category.assoc]
  have e1 : spMap ((intO ↥y.C.S).subtype.comp ψ) ≫ U.toX ≫ h = y.gen := by
    rw [← Category.assoc, e0, LocM.Mdl.Pt.gen, ← hψ]; simp only [Category.assoc]
  have e2 : spMap ((intO ↥y.C.S).subtype.comp ψ) ≫ U.toX ≫ h ≫ Z.π = y.gen ≫ Z.π := by
    rw [← e1]; simp only [Category.assoc]
  have hab : Set.range (spMap ((intO ↥y.C.S).subtype.comp ψ) ≫ U.toX ≫ h ≫ Z.π) ⊆ abLocus (Y Z.i).t.G := by
    rw [e2, LocM.Mdl.Pt.gen, Category.assoc, y.z_π, y.P.ext]
    rintro _ ⟨q, rfl⟩
    exact GlobalTheory.ModelScope.range_j_subset_abLocus _ ⟨y.P.y q, rfl⟩
  have k := hH E H Dw p _ (Y Z.i).t (GlobalTheory.ShFam.Pad.Pull.isSeparated_base Z.i) U.Bp _ t φt hφt GG act pol θ ε τ hP n e b c hc
    (fun j => lam (η j)) hη r u hu y.C ψ hab _ v (hco _ _ a φ (hφ.trans e1.symm) cf v (e2 ▸ hv))
  have hr : ∀ w l, (lam w).1 (u l) = fb.repr w l := fun w l => by
    conv_lhs => rw [← fb.sum_repr w, map_sum, AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
    simp only [map_smul, hfb, SetLike.val_smul, Pi.smul_apply, hd, smul_eq_mul]
    simp
  rw [e2, e0] at k
  simp only [hr] at k
  obtain rfl : A = _ := funext hA
  exact k

set_option maxHeartbeats 800000 in

theorem pt_conds (hT : TanSt) (hH : HTSt) (h6 : KerRSt) [IsLocallyNoetherian (Y Z.i).X] (hx : Function.Bijective x)
    (k : IsEqLat Z h x true Om s) (U : AffOp B.X) {t : SAB H (Sp U.Bp)} {φt : t.G.left ⟶ (Y Z.i).t.G.left}
    (hφt : IsGrpPullback t.G (Y Z.i).t.G (U.toX ≫ h ≫ Z.π) φt) {lam : SecBp Om.V U →ₗ[U.Bp] Pdiv.omega t.G}
    (hb : Function.Bijective lam) (hl : FormLink Z h x k.2.2.1.frame U φt lam) {GG : PDivGroup p U.Bp}
    {act : PDivGroup.Action (𝓞 E) GG} {pol : GG ≅ GG.dual} {θ : TorsionMap t.G GG} {ε : (PDivGroup.mu p U.Bp).Tate}
    {τ : Dw.La →+ GG.Tate} (hP : IsPropG Dw t GG act pol θ ε τ) {n : ℕ} (e : GG.height = n)
    (b : Module.Basis (Fin n) ℤ Dw.La) {c : Pdiv.omega t.G →ₗ[U.Bp] GG.omega} (hc : θ.IsOmega c) {η : Fin n → SecBp Om.V U}
    (hη : IsDlog (ct hP e b) e (c ∘ₗ lam) η) {pr : SecBp (GlobalTheory.VB.dual Om.V) U →ₗ[U.Bp] Module.Dual U.Bp (SecBp Om.V U)}
    (hpv : ∀ y w, pr (1 ⊗ₜ y) (1 ⊗ₜ w) = algebraMap Γ(B.X, U.1) U.Bp (GlobalTheory.VB.dualApp y le_rfl w)) {o : ℕ} {π : Γ(B.X, ⊤)}
    {γ : ℕ → U.Bp} (C : RChain p U.Bp n o (cstBp U π) γ (SecBp (GlobalTheory.VB.dual Om.V) U) (SecBp Om.V U))
    (hJ : ∀ y (q : C.L 0), C.j y = Submodule.Quotient.mk q ↔ ∀ j, cstBp U π ∣ q.1 j - pr y (η j))
    (hR : ∀ w, C.ρ w = 0 ↔ w ∈ Submodule.span U.Bp (Set.range η) ⊔ (p : U.Bp) • (⊤ : Submodule U.Bp (SecBp Om.V U)))
    (hdv : cstBp U π ∣ (p : U.Bp)) (y : Z.Pt)
    (ψ : U.Bp →+* ↥(intO ↥y.C.S)) (hψ : (spMap ψ ≫ U.toX) ≫ h = y.z) (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S)
    (hφ : spMap φ ≫ Z.chart a = y.gen) :
    (∀ (e : Fin r → Γ(GlobalTheory.VB.dual Om.V, U.1)) (he : GlobalTheory.VB.IsFrame e),
      JCond Z h x (fun a => (k.2.2.1.frame a).dual) π y (spMap ψ ≫ U.toX) a φ he (C.kerJ ψ fun l => 1 ⊗ₜ e l)) ∧
    ∀ (e : Fin r → Γ(Om.V, U.1)) (he : GlobalTheory.VB.IsFrame e),
      RCond Z h (fun i => x i.rev) (isEqLat_rev k).2.2.1.frame y (spMap ψ ≫ U.toX) a φ he (C.kerR ψ fun l => 1 ⊗ₜ e l) := by
  have h0 : ψ (cstBp U π) ≠ 0 := fun h0 => by
    have k0 := map_dvd ((intO ↥y.C.S).subtype.comp ψ) hdv
    rw [map_natCast, RingHom.comp_apply, h0, map_zero, zero_dvd_iff] at k0
    exact (Fact.out : p.Prime).ne_zero (Nat.cast_eq_zero.1 k0)
  have hfb : ∀ {f : Fin r → Γ(Om.V, U.1)} (hf : GlobalTheory.VB.IsFrame f) (l : Fin r),
      (hf.basis le_rfl).baseChange U.Bp l = 1 ⊗ₜ f l := fun hf l => by
    rw [Module.Basis.baseChange_apply, hf.basis_apply, GlobalTheory.Twist.resM_self]
  refine ⟨fun e he cf v hv => ?_, fun f hf cf v hv => ?_⟩
  · obtain ⟨f, hf, rfl⟩ := exists_predual k.2.1 he
    have k1 := mem_lat_iff hT hH hx k.2.2.1.frame U hφt hb hl hP e b hc hη hf _ (hfb hf) y ψ hψ a φ hφ cf v hv _ fun _ => rfl
    have k2 := cut_iff_kerJ C ψ ((hf.basis le_rfl).baseChange U.Bp)
      (fun l => ∑ i, cf i * valF (spMap (intO ↥y.C.S).subtype ≫ spMap ψ ≫ U.toX) _ (coef true hf (k.2.2.1.frame a) l i))
      hR (fun l => 1 ⊗ₜ hf.coord l) (fun l q hq j => by
        have e := coord_ext (hf.basis le_rfl) l (pr (1 ⊗ₜ hf.coord l)) (fun w =>
          (hpv _ _).trans (congrArg _ (hf.dualApp_coord l le_rfl w))) (η j)
        exact e ▸ (hJ _ q).1 hq j) hdv h0
    have k3 : valF (spMap (intO ↥y.C.S).subtype ≫ spMap ψ ≫ U.toX) ⊤ π = (ψ (cstBp U π) : ↥y.C.S) := by
      rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp, valF_toX]
      rfl
    refine (k1.trans k2).trans (exists_congr fun c => and_congr_right fun _ => forall_congr' fun l => Eq.congr_right ?_)
    exact congrArg₂ (· * ·) k3.symm (Finset.sum_congr rfl fun i _ =>
      congrArg (fun q => cf i * valF _ _ q) (coef_dual hf (k.2.2.1.frame a) l i).symm)
  · have hK := h6 p U.Bp _ o _ _ _ _ C _ ψ h0 r ((hf.basis le_rfl).baseChange U.Bp)
    have k1 := mem_lat_iff hT hH hx k.2.2.1.frame U hφt hb hl hP e b hc hη hf _ (hfb hf) y ψ hψ a φ hφ _ v
      (comb_perm' _ _ Fin.revPerm (fun i => (Z.fr a).bc φ (x i).1 (x i).2) cf v hv) _ fun _ => rfl
    have k2 := k1.trans (cut_iff_kerR C ψ _ _ hR hK)
    rw [show ⇑((hf.basis le_rfl).baseChange U.Bp) = fun l => 1 ⊗ₜ f l from funext (hfb hf)] at k2
    refine k2.trans (forall₂_congr fun c _ => Eq.to_iff (congrArg (fun q : ↥y.C.S => ‖q‖ ≤ 1)
      (Finset.sum_congr rfl fun l _ => congrArg ((c l : ↥y.C.S) * ·) ?_)))
    refine (Equiv.sum_comp Fin.revPerm _).symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    exact congrArg₂ (fun j q => cf j * valF _ _ q) (Equiv.symm_apply_apply _ i)
      (repr_perm (k.2.2.1.frame a) Fin.revPerm ((isEqLat_rev k).2.2.1.frame a) _ _ i).symm

set_option maxHeartbeats 1600000 in

theorem exists_sys (h1 : RingExSt) (h2 : RingResSt) (h3 : RingActSt) (h4 : RingJSt) (h5 : RingRSt) (h6 : KerRSt)
    (h7 : OmegaResSt) (hH : HTSt) (h8 : RootSt) (h9 : PairSt) (h10 : FormResSt) (h11 : FormActSt) (hT : TanSt)
    (D : PrismData p) [IsLocallyNoetherian (Y Z.i).X] (hx : Function.Bijective x) (ho : ToOpen Z h)
    (k : IsEqLat Z h x true Om s)
    (hF : ∀ (U : AffOp B.X) (t : SAB H (Sp U.Bp)) (φt : t.G.left ⟶ (Y Z.i).t.G.left),
      IsGrpPullback t.G (Y Z.i).t.G (U.toX ≫ h ≫ Z.π) φt →
        ∃ lam : SecBp Om.V U →ₗ[U.Bp] Pdiv.omega t.G, Function.Bijective lam ∧ FormLink Z h x k.2.2.1.frame U φt lam)
    (hG : PropGOn Dw p h Z.t) (o : ℕ) {ζ : Γ(B.X, ⊤)} (hζ : IsPrimitiveRoot ζ (p ^ (o + 2))) :
    ∃ (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (n : ℕ) (M : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ)
      (C : ChainsBp p n o (dualA H.bar Om) Om π γ), IsRootOfP p π (p - 1) ∧ (∀ k ≤ o, IsRootOfP p (γ k) (p ^ (k + 1))) ∧
        IsSys C M ∧ SysPt Z h x (fun i => x i.rev) (isEqLat_dual k).2.2.1.frame (isEqLat_rev k).2.2.1.frame C := by
  obtain ⟨t, ⟨m⟩⟩ := exists_pullbacks h Z.t
  obtain ⟨GG, act, pol, θ, ε, τ, hP, hR⟩ := hG t m
  have kL := GlobalTheory.Coisotropic.lattice_rank E H Dw
  haveI := kL.1
  haveI := kL.2.1
  have b := Module.finBasisOfFinrankEq ℤ _ kL.2.2
  haveI := charZero_kbar ho
  obtain ⟨π, γ, hπ, hγ, hz⟩ := h8 O B p o ζ (fun U n => muRoot (ε U) n) hζ (fun U => (hP U).prim)
    fun U U' hle => (hR U U' hle).1
  have hpb : ∀ U : AffOp B.X, IsGrpPullback (t U).G (Y Z.i).t.G (U.toX ≫ h ≫ Z.π) ((m U).φ ≫ Z.tMap.φ) := fun U => by
    simpa only [Category.assoc] using (m U).cart.comp Z.tMap.cart
  choose lam hb hl using fun U => hF U (t U) _ (hpb U)
  choose c hc hca using fun U => (hP U).omega
  choose hfin hprj pr hpr hpv using h9 B.X Om.V r k.2.1
  have hL := h9 B.X _ r k.2.1.dual
  have hlev : ∀ U, IsLevels (c U ∘ₗ lam U) := fun U => ⟨fun n => (hc U n).1.comp (hb U).2, fun n w =>
    ((hc U n).2.1 (lam U w)).trans ⟨fun ⟨w', hw⟩ => by
      obtain ⟨w', rfl⟩ := (hb U).2 w'
      exact ⟨w', (hb U).1 (hw.trans (map_smul _ _ _).symm)⟩, fun ⟨w', hw⟩ => ⟨lam U w', by rw [hw, map_smul]⟩⟩⟩
  have hdv : ∀ U, cstBp U π ∣ (p : U.Bp) := fun U => by
    obtain ⟨u, hu⟩ := hπ
    have h0 : π ∣ (p : Γ(B.X, ⊤)) := (Units.dvd_mul_left (u := u)).1
      (hu ▸ dvd_pow_self π (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt))
    have h1 := map_dvd ((algebraMap Γ(B.X, U.1) U.Bp).comp (resG B.X le_top)) h0
    rwa [map_natCast] at h1
  choose C hC using fun U : AffOp B.X =>
    @h1 p _ D U.Bp (Kbar B.X) _ _ _ _ _ _ _ _ (GG U) (pol U) (ε U) (ct (hP U) (hP U).height b) _ o (hP U).height (cstBp U π)
      (fun n => cstBp U (γ n)) (SecBp (dualA H.bar Om).V U) (SecBp Om.V U) _ _ _ _ (hL U).1 (hL U).2.1 (hfin U) (hprj U)
      (c U ∘ₗ lam U) (pr U) (hP U).prim (hlev U) (hpr U) (hz U).1 (hz U).2
  refine ⟨π, γ, _, actMat b, C, hπ, hγ, ⟨fun U U' hle => ?_, fun U a => ?_⟩, fun y U ψ hψ a φ hφ => ?_⟩
  · letI := (AffOp.res hle).toAlgebra
    obtain ⟨hε, f, -, hpol, hτ, hθ⟩ := hR U U' hle
    obtain ⟨l, hl1⟩ := exists_res (GlobalTheory.VB.dual Om.V) hle
    obtain ⟨m', hm1⟩ := exists_res Om.V hle
    have a0 : IsGrpPullback (t U').G Z.t.G (spMap (algebraMap U.Bp U'.Bp) ≫ U.toX ≫ h) (m U').φ := by
      rw [← Category.assoc, show spMap (algebraMap U.Bp U'.Bp) ≫ U.toX = U'.toX from AffOp.res_toX hle]
      exact (m U').cart
    have a1 := semi_ext (σ := algebraMap U.Bp U'.Bp) m' (c U' ∘ₗ lam U') (c U ∘ₗ lam U) ((GG U).toBase U'.Bp).omega
      (omegaMap _ _ f.hom) fun σ => (congrArg (c U' ∘ₗ lam U') (hm1 σ)).trans
        (h7 E H p Z.X Z.t U.Bp U'.Bp _ (t U) (t U') _ _ (m U).cart a0 _ _ _ _ (c U) (c U') f (hc U) (hc U') hθ
          (lam U (1 ⊗ₜ σ)) (lam U' (1 ⊗ₜ resM Om.V hle σ)) fun v v' hv =>
            h10 E H Dw Xo p W Y i₀ Z B.X h r x hx ho Om.V s _ U U' hle _ _ _ _ (hpb U) _ _ (hl U) (hl U') σ v v'
              ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Z.tMap.φ) hv).trans (by
                simp only [Category.assoc]
                try rfl))))
    have a2 := pair_ext (σ := algebraMap U.Bp U'.Bp) (pr U) (pr U') l m' fun y w =>
      (congrArg₂ (fun y w => pr U' y w) (hl1 y) (hm1 w)).trans ((hpv U' _ _).trans (Eq.trans (by
        rw [GlobalTheory.VB.dualApp_res, GlobalTheory.VB.dualApp_resM y le_rfl hle]
        exact (res_algebraMap hle _).symm) (congrArg (AffOp.res hle) (hpv U y w)).symm))
    have a3 : cstBp U' π = algebraMap U.Bp U'.Bp (cstBp U π) := by rw [(hz U).1, (hz U').1, map_sub, map_one, hε]
    have k2 := h2 E H Dw p D U.Bp U'.Bp _ _ _ _ _ _ _ (hP U) _ _ _ _ _ _ _ (hP U') _ o _ _ b _ _ _ _ _ _ _ _ _ _ _ _
      (C U) (C U') f l m' (hC U) (hC U') hε hpol hτ a1 a2 (hdv U) a3
    exact ⟨k2.1, l, m', hl1, hm1, k2.2⟩
  · have hm := fun a : 𝓞 E => lin_ext (c U ∘ₗ lam U) (appLinear (Om.ρ a : Om.V ⟶ Om.V) U.1)
      (omegaMap _ _ (act U (H.bar a))) fun σ => hca U _ _ _
        (h11 E H Dw Xo p W Y i₀ Z O B h r x hx ho Om s k U _ _ (hpb U) (fun a => by
          rw [← Category.assoc, (m U).act, Category.assoc, Z.tMap.act, Category.assoc]) _ (hl U) a σ)
    have a2 := adj_ext (pr U) (appLinear (GlobalTheory.VB.dualMap (Om.ρ (H.bar a) : Om.V ⟶ Om.V)) U.1)
      (appLinear (Om.ρ (H.bar a) : Om.V ⟶ Om.V) U.1) fun y w =>
        (hpv U _ _).trans ((congrArg _ (GlobalTheory.VB.dualApp_dualMap _ y le_rfl w)).trans (hpv U _ _).symm)
    have a3 := hm (H.bar a)
    rw [bar_bar] at a3
    exact ⟨(appLinear (GlobalTheory.VB.dualMap (Om.ρ (H.bar a) : Om.V ⟶ Om.V)) U.1).baseChange U.Bp,
      (appLinear (Om.ρ a : Om.V ⟶ Om.V) U.1).baseChange U.Bp, fun _ => LinearMap.baseChange_tmul _ _ _,
      fun _ => LinearMap.baseChange_tmul _ _ _,
      h3 E H Dw p D U.Bp _ _ _ _ _ _ _ (hP U) _ o _ b _ _ _ _ _ _ (C U) a _ _ _ (hC U) (hm a)
        a3 a2 (hdv U)⟩
  · choose η hη using fun j => (hlev U).1 1 ((dlog (GG U) ((ct (hP U) (hP U).height b).t' (Fin.cast (hP U).height.symm j))).1 1)
    have hJ := h4 p D U.Bp _ _ _ _ _ o _ _ _ _ _ _ _ (C U) η (hC U) (hlev U) hη (hdv U)
    have hR' := @h5 E _ _ _ H Dw p _ D U.Bp _ _ _ _ _ _ _ _ (hP U) _ o _ b _ _ _ _ _ _ _ _ (hfin U) (hprj U) _ _ (C U) η (hC U) (hlev U) hη (hdv U)
    exact pt_conds hT hH h6 hx k U (hpb U) (hb U) (hl U) (hP U) _ b (hc U) hη (hpv U) (C U) hJ hR' (hdv U) y ψ hψ a φ hφ

theorem isLocallyNoetherian_base (Z : LocM.Mdl Y i₀) [IsDiscreteValuationRing (Z.i.c.V W)] : IsLocallyNoetherian (Y Z.i).X :=
  haveI : IsProper (Y Z.i).s := projProper _ _ _ (Y Z.i).proj
  LocallyOfFiniteType.isLocallyNoetherian (Y Z.i).s

theorem exists_sys_bundles (h1 : RingExSt) (h2 : RingResSt) (h3 : RingActSt) (h4 : RingJSt) (h5 : RingRSt) (h6 : KerRSt)
    (h7 : OmegaResSt) (hH : HTSt) (h8 : RootSt) (h9 : PairSt) (hA : ActSt) (hF : FormSt) (h10 : FormResSt) (h11 : FormActSt)
    (hT : TanSt) (D : PrismData p) [IsLocallyNoetherian (Y Z.i).X] (hx : Function.Bijective x) (ho : ToOpen Z h)
    (hG : PropGOn Dw p h Z.t) (o : ℕ) {ζ : Γ(B.X, ⊤)} (hζ : IsPrimitiveRoot ζ (p ^ (o + 2))) :
    ∃ (Lie Om : AM B (𝓞 E)) (sL : _) (sO : _) (hL : IsEqLat Z h x false Lie sL)
      (hO : IsEqLat Z h (fun k => x k.rev) true Om sO) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (n : ℕ)
      (M : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ) (C : ChainsBp p n o Lie Om π γ), IsRootOfP p π (p - 1) ∧
        (∀ k ≤ o, IsRootOfP p (γ k) (p ^ (k + 1))) ∧ IsSys C M ∧
          SysPt Z h x (fun k => x k.rev) hL.2.2.1.frame hO.2.2.1.frame C := by
  haveI := (GlobalTheory.TanSec.isVB_om E H Dw Xo p W Y i₀ Z r x hx).dual.isQuasicoherent
  have hfr : ∀ a, GlobalTheory.VB.IsFrame (GlobalTheory.TanSec.secX Z h x a) := fun a =>
    (GlobalTheory.TanSec.Frame.isFrame_sec E H Dw Xo p W Y i₀ Z r x hx a).pullback h
  obtain ⟨ρ, k⟩ := hA E H Dw Xo p W Y i₀ Z O B h r x hx hfr
  exact ⟨_, _, _, _, isEqLat_dual k, isEqLat_rev k, exists_sys h1 h2 h3 h4 h5 h6 h7 hH h8 h9 h10 h11 hT D hx ho k
    (hF E H Dw Xo p W Y i₀ Z B.X h r x hx hfr) hG o hζ⟩

end Main

theorem sysCoverSt_of_steps (h1 : RingExSt) (h2 : RingResSt) (h3 : RingActSt) (h4 : RingJSt) (h5 : RingRSt) (h6 : KerRSt)
    (h7 : OmegaResSt) (hH : HTSt) (h8 : RootSt) (h9 : PairSt) (hA : ActSt) (hF : FormSt) (h10 : FormResSt) (h11 : FormActSt)
    (hT : TanSt) (hD : GlobalTheory.Published.PrismaticDieudonnePerfd) (hG : GlobalTheory.GroupBplus.GroupAllSt) : SysCoverSt := by
  intro D O hO p _ W hW jc hj z
  haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
  intro c o B f hB hf ⟨ζ, hζ⟩
  obtain ⟨P⟩ := PrismData.nonempty hD p
  haveI := isLocallyNoetherian_base z.Z
  exact exists_sys_bundles h1 h2 h3 h4 h5 h6 h7 hH h8 h9 hA hF h10 h11 hT P (xAll_bijective O.S)
    (GlobalTheory.TestPts.mem_opn_comp Fact.out hW f) (hG D O hO p W hW jc hj z c B f hB hf) o hζ

end GlobalTheory.ChainPts.SysB

end
