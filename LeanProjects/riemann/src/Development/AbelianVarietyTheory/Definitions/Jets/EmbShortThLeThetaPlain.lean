import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormTies

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open scoped TensorProduct

def levFull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (l : Level H)
    (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) : (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La) :=
  (liftLa γ, LinearMap.id)

variable {D : D7}

def thetaPlain {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) :
    Submodule (𝓞 B.KO) X.Forms :=
  X.emb wL (X.thAll wL) ^ T * X.emb wF (X.shortTh wF) ⊔
    X.emb wL (X.thAll wL) ^ (T - WeightFamilies.dimY D j) * X.emb (X.wF0 wL wF) (X.shortTh (X.wF0 wL wF)) ⊔
    X.emb ka (X.shortTh ka)

def sigRec (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) {j : ℕ} (ka wL wF : WeightFamilies.Wt D j)
    (T : ℕ) : 𝓞 B.KO :=
  nnW B hinj EX ka * (((D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * wF.n) *
    pPow D (T * c2 D wL + c2 D wF) (T * cHalf wL + cHalf wF) (T * cHalf wL + cHalf wF) : ℕ) : 𝓞 B.KO)

def spanK {F : Type} [Field F] {K : Type} [Field K] [NumberField K] [Algebra F K] {C : Type} [AddCommGroup C] [Module F C]
    {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (s : Set C) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.span (𝓞 K) ((fun f : C => z.symm (1 ⊗ₜ[F] f)) '' s)

structure FormTie {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P6 j)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra B.KO K]
    {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J)
    (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka) : Prop where
  Ms_eq : O.Ms i = spanK z (B.Mlat j ka : Set _)
  rho_eq : ∀ (g : P) (F : B.Cusp j ka), O.ρ i g (z.symm (1 ⊗ₜ F)) = z.symm (1 ⊗ₜ act g F)
  Th_eq : O.Th v i = spanK z {F | X.inc ka F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T}
  σ_eq : O.σ v i = algebraMap B.KO K (sigRec B hinj EX ka wL wF T : 𝓞 B.KO)
  ThK_fg : (O.ThK v i).FG
  ThK_ge : spanK z {F | X.inc ka F ∈ thetaPlain X ka wL wF T} ≤ O.ThK v i

def IsLevAct (T : Top D) (h : LawsP T) (j : ℕ) (w : WeightFamilies.Wt D j) {P : Type}
    (ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l))
    (act : P → (recB h.toLawsCore).Cusp j w → (recB h.toLawsCore).Cusp j w) : Prop :=
  ∀ g F, ((act g F).1 : T.R j) = actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) (ℓ g) F.1

structure FormTieK {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P6 j)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra B.KO K]
    {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J)
    (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka) : Prop where
  Ms_eq : O.Ms i = spanK z (B.Mlat j ka : Set _)
  rho_eq : ∀ (g : P) (F : B.Cusp j ka), O.ρ i g (z.symm (1 ⊗ₜ F)) = z.symm (1 ⊗ₜ act g F)
  Th_eq : O.Th v i = spanK z {F | X.inc ka F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T}
  σ_eq : O.σ v i = algebraMap B.KO K (sigRec B hinj EX ka wL wF T : 𝓞 B.KO)
  ThK_eq : O.ThK v i = spanK z (X.shortTh ka : Set _)

def ProductsShort {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) : Prop :=
  thetaPlain X ka wL wF T ≤ X.emb ka (X.shortTh ka)

def withCoeff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n n' : ℕ} (d : DeltaDat Xo c n)
    (φ : (Fin n' → LevQ Dw d.l₂) → c.F) : DeltaDat Xo c n' :=
  ⟨d.pd, d.I, d.l₂, d.Xo₂, d.c₂, d.hF, d.r, d.m, d.nab₂, d.cδ, φ⟩

def OneCover (T : Top D) (j : ℕ) : Prop :=
  ∀ n, ∃ φ, T.dδ j n = withCoeff (T.dδ j 0) φ

section Span

variable {F : Type} [Field F] {K : Type} [Field K] [NumberField K] [Algebra F K] {C : Type} [AddCommGroup C] [Module F C]
  {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C)

theorem spanK_mono {s t : Set C} (h : s ⊆ t) : spanK z s ≤ spanK z t :=
  Submodule.span_mono (Set.image_mono h)

theorem mem_spanK {s : Set C} {f : C} (hf : f ∈ s) : z.symm (1 ⊗ₜ[F] f) ∈ spanK z s :=
  Submodule.subset_span ⟨f, hf, rfl⟩

theorem spanK_fg_of_fg [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] {N : Submodule (𝓞 F) C} (hN : N.FG) :
    (spanK z (N : Set C)).FG := by
  obtain ⟨t, rfl⟩ := hN
  have key : spanK z (Submodule.span (𝓞 F) (t : Set C) : Set C) = spanK z (t : Set C) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (spanK_mono z Submodule.subset_span)
    rintro _ ⟨f, hf, rfl⟩
    change z.symm (1 ⊗ₜ[F] f) ∈ spanK z (t : Set C)
    induction hf using Submodule.span_induction with
    | mem x hx => exact mem_spanK z hx
    | zero => simp
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add]; exact add_mem hx hy
    | smul r x _ hx =>
      have e : (1 : K) ⊗ₜ[F] (r • x) = (algebraMap F K (r : F)) • ((1 : K) ⊗ₜ[F] x) := by
        have h1 : r • x = (r : F) • x := (algebraMap_smul F r x).symm
        rw [h1, TensorProduct.tmul_smul, algebraMap_smul K]
      rw [e, map_smul]
      exact (spanK z (t : Set C)).smul_mem (algebraMap (𝓞 F) (𝓞 K) r) hx
  rw [key]
  exact Submodule.fg_span (t.finite_toSet.image _)

example : spanK z (∅ : Set C) = ⊥ := by simp [spanK]

example : spanK z ({0} : Set C) = ⊥ := by simp [spanK]

end Span

section Short

variable {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem runScalar_kappa_ne_zero (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) {p : ℕ} (hp : 0 < p)
    (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) : (scalOfP B hinj EX p ka wL wF T).sK ≠ 0 := by
  have hn : ∀ i, EX.piG i * piBarO EX i = (D.host.g i : 𝓞 D.host.E) := fun i => Subtype.ext (EX.piG_norm i)
  have hn' : ∀ i, iE D hinj B (EX.piG i) * iE D hinj B (piBarO EX i) ≠ 0 := fun i => by
    rw [← map_mul, hn, map_natCast]
    exact_mod_cast (D.host.g_prime i).ne_zero
  have hnn : ∀ w : WeightFamilies.Wt D j, nnW B hinj EX w ≠ 0 := fun w => Finset.prod_ne_zero_iff.2 fun i _ =>
    mul_ne_zero (pow_ne_zero _ (left_ne_zero_of_mul (hn' i))) (pow_ne_zero _ (right_ne_zero_of_mul (hn' i)))
  have hQ : D.host.QS ≠ 0 := D.host.QS_pos.ne'
  have hq : D.host.q ≠ 0 := (D.host.hyp.1 : D.host.q.Prime).ne_zero
  have hd : D.host.d ≠ 0 := (D.host.hyp.2.1 : D.host.d.Prime).ne_zero
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 ?_) (pow_ne_zero _ (hnn wL))) (hnn wF))
    (Nat.cast_ne_zero.2 ?_)
  · exact pow_ne_zero _ hp.ne'
  · unfold pPow
    positivity

theorem shortTh_fg_of_Thc_le (X : WeightAlgebra.PJ D B P6 j) (w : WeightFamilies.Wt D j) {s : 𝓞 B.KO} (hs : s ≠ 0)
    (hle : X.Thc s w ≤ B.Mlat j w) (hM : (B.Mlat j w).FG) : (X.shortTh w).FG := by
  set t : 𝓞 B.KO := ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * w.n) with ht
  have ht0 : t ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero))
  have hinj : ∀ a : 𝓞 B.KO, a ≠ 0 →
      Function.Injective (a • (LinearMap.id : B.Cusp j w →ₗ[𝓞 B.KO] B.Cusp j w)) := by
    intro a ha x y hxy
    have ha' : (a : B.KO) ≠ 0 := fun h => ha (RingOfIntegers.coe_eq_zero_iff.1 h)
    have e : (a : B.KO) • x = (a : B.KO) • y :=
      (algebraMap_smul B.KO a x).trans ((show a • x = a • y from hxy).trans (algebraMap_smul B.KO a y).symm)
    exact smul_right_injective _ ha' e
  have h1 : (X.Thc s w).FG := hM.of_le hle
  exact Submodule.fg_of_fg_map_injective _ (hinj t ht0) (Submodule.fg_of_fg_map_injective _ (hinj s hs) h1)

theorem shortTh_fg (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) {p : ℕ} (hp : 0 < p)
    (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (hM : Submodule.IsLattice B.KO (B.Mlat j ka))
    (h2 : WeightAlgebra.H2 X (scalOfP B hinj EX p ka wL wF T) ka wL wF) : (X.shortTh ka).FG :=
  shortTh_fg_of_Thc_le X ka (runScalar_kappa_ne_zero hinj EX hp ka wL wF T) h2.2.2.2 hM.fg

theorem ProductsShort.mem {X : WeightAlgebra.PJ D B P6 j} {ka wL wF : WeightFamilies.Wt D j} {T : ℕ} (h : ProductsShort X ka wL wF T)
    {F : B.Cusp j ka} (hF : X.inc ka F ∈ thetaPlain X ka wL wF T) : F ∈ X.shortTh ka := by
  obtain ⟨G, hG, e⟩ := Submodule.mem_map.1 (h hF)
  exact X.inc_inj ka e ▸ hG

variable {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra B.KO K]
  {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}

theorem FormTieK.toFormTie {X : WeightAlgebra.PJ D B P6 j} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
    {ka wL wF : WeightFamilies.Wt D j} {T : ℕ} {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 K)} {i : Bs.J}
    {z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka} {act : P → B.Cusp j ka → B.Cusp j ka}
    (h : FormTieK X hinj EX p ka wL wF T O v i z act) (hfg : (X.shortTh ka).FG)
    (hpr : ProductsShort X ka wL wF T) : FormTie X hinj EX p ka wL wF T O v i z act :=
  ⟨h.Ms_eq, h.rho_eq, h.Th_eq, h.σ_eq, h.ThK_eq ▸ spanK_fg_of_fg z hfg,
    h.ThK_eq ▸ spanK_mono z fun _ hF => hpr.mem hF⟩

theorem FormTieK.rho_tmul {X : WeightAlgebra.PJ D B P6 j} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
    {ka wL wF : WeightFamilies.Wt D j} {T : ℕ} {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 K)} {i : Bs.J}
    {z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka} {act : P → B.Cusp j ka → B.Cusp j ka}
    (h : FormTieK X hinj EX p ka wL wF T O v i z act) (g : P) (a : K) (F : B.Cusp j ka) :
    O.ρ i g (z.symm (a ⊗ₜ F)) = z.symm (a ⊗ₜ act g F) := by
  have e : ∀ G : B.Cusp j ka, (a ⊗ₜ[B.KO] G : K ⊗[B.KO] B.Cusp j ka) = a • (1 ⊗ₜ[B.KO] G) := fun G => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e, e, map_smul, map_smul, map_smul, h.rho_eq]

end Short

def repCoord {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] {C : Type} [AddCommGroup C] [Module F C]
    {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) {P : Type} [Group P] (ρ : Representation F P C) :
    Representation K P (Fin n → K) where
  toFun g := z.symm.toLinearMap ∘ₗ (ρ g).baseChange K ∘ₗ z.toLinearMap
  map_one' := by
    refine LinearMap.ext fun x => ?_
    simp [Module.End.one_eq_id]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    simp [Module.End.mul_eq_comp, LinearMap.baseChange_comp]

theorem exists_formTieK {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra B.KO K]
    {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    (O : OnObj S P oc) (jj : Bs.J → ℕ) (X : HeightOneSpectrum (𝓞 K) → ∀ i, WeightAlgebra.PJ D B P6 (jj i))
    (p : HeightOneSpectrum (𝓞 K) → ℕ) (ka wL wF : ∀ i, WeightFamilies.Wt D (jj i)) (T : ℕ)
    (ρ : ∀ i, Representation B.KO P (B.Cusp (jj i) (ka i))) :
    ∃ (O' : OnObj S P oc) (z : ∀ i, (Fin (O'.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp (jj i) (ka i)),
      (∀ i, O'.nZ i = Module.finrank B.KO (B.Cusp (jj i) (ka i))) ∧ O'.pde = O.pde ∧ O'.U = O.U ∧
      ∀ v i, FormTieK (X v i) hinj EX (p v) (ka i) (wL i) (wF i) T O' v i (z i) (fun g F => ρ i g F) := by
  let z : ∀ i, (Fin (Module.finrank B.KO (B.Cusp (jj i) (ka i))) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp (jj i) (ka i) :=
    fun i => ((Module.finBasis B.KO (B.Cusp (jj i) (ka i))).baseChange K).equivFun.symm
  let O' : OnObj S P oc :=
    { O with
      nZ := fun i => Module.finrank B.KO (B.Cusp (jj i) (ka i))
      ρ := fun i => repCoord (z i) (ρ i)
      V₀ := fun _ => ⊥
      e := fun _ => 0
      Ms := fun i => spanK (z i) (B.Mlat (jj i) (ka i) : Set _)
      φ := fun _ => 0
      Th1 := fun _ _ => ⊥
      Th := fun v i => spanK (z i) {F | (X v i).inc (ka i) F ∈
        (X v i).Theta (scalOfP B hinj EX (p v) (ka i) (wL i) (wF i) T) (ka i) (wL i) (wF i) T}
      ThK := fun v i => spanK (z i) ((X v i).shortTh (ka i) : Set _)
      Th0 := fun _ _ => ⊥
      ThJ := fun _ _ => ⊥
      X₃ := fun _ _ => ⊥
      σ := fun _ i => algebraMap B.KO K (sigRec B hinj EX (ka i) (wL i) (wF i) T : 𝓞 B.KO)
      θ' := fun _ _ => 0 }
  refine ⟨O', z, fun _ => rfl, rfl, rfl, fun v i => ⟨rfl, fun g F => ?_, rfl, rfl, rfl⟩⟩
  change (z i).symm ((ρ i g).baseChange K (z i ((z i).symm _))) = _
  rw [LinearEquiv.apply_symm_apply, LinearMap.baseChange_tmul]

theorem OneCover.eq_withCoeff {T : Top D} {j : ℕ} (h : OneCover T j) (n n' : ℕ) :
    ∃ φ, T.dδ j n' = withCoeff (T.dδ j n) φ := by
  obtain ⟨φ, e⟩ := h n
  obtain ⟨φ', e'⟩ := h n'
  rw [e, e']
  exact ⟨φ', rfl⟩

def topOfCover (T : Top D) {m : ℕ → ℕ} (d : ∀ j, DeltaDat (T.Q.Xo j) T.Q.c (m j))
    (φ : ∀ j n, (Fin n → LevQ (T.Q.Dw j) (d j).l₂) → T.Q.c.F) : Top D :=
  { T with dδ := fun j n => withCoeff (d j) (φ j n) }

end GlobalTheory.FormTies
