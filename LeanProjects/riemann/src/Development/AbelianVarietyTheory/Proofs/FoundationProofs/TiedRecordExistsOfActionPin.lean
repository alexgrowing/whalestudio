import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRepIsLevAct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnTies

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

structure RunData (J : CoreJ D) : Type 1 where

  loc : In66 J.Q

  nab : ∀ j, NabV (J.Q.Xo j) J.Q.c

  dδ : ∀ j n, DeltaDat (J.Q.Xo j) J.Q.c n

  xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ

  half₂ : Ideal (𝓞 D.host.E)

abbrev RunData.full {J : CoreJ D} (r : RunData J) : Full D :=
  ⟨⟨J.toCore, r.loc, r.nab, r.dδ⟩, J.cE, J.chiW, J.x₀, J.iota, r.xi, r.half₂⟩

def RunData.ofFull (T : Full D) : RunData T.J := ⟨T.G, T.nab, T.dδ, T.xi, T.half₂⟩

theorem RunData.full_ofFull (T : Full D) : (RunData.ofFull T).full = T := rfl

theorem RunData.full_J {J : CoreJ D} (r : RunData J) : r.full.J = J := rfl

theorem RunData.exists_full_eq_iff (J : CoreJ D) (T : Full D) : (∃ r : RunData J, r.full = T) ↔ T.J = J :=
  ⟨by rintro ⟨r, rfl⟩; rfl, by rintro rfl; exact ⟨RunData.ofFull T, rfl⟩⟩

section Cusp

variable (B : WeightFamilies.Prov D) {j : ℕ} {w : WeightFamilies.Wt D j} {K : Type} [Field K] [NumberField K] [Algebra B.KO K] {n : ℕ}

def supSpan (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) : Submodule (𝓞 K) (Fin n → K) := spanK z (B.Mlat j w : Set _)

def shortSpan {P6 : ModuliIntegralCharts.Prov D} (X : WeightAlgebra.PJ D B P6 j) (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) :
    Submodule (𝓞 K) (Fin n → K) := spanK z (X.shortTh w : Set _)

def scaledSpan {P6 : ModuliIntegralCharts.Prov D} (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (wL wF : WeightFamilies.Wt D j) (nT : ℕ) (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) : Submodule (𝓞 K) (Fin n → K) :=
  spanK z {F | X.inc w F ∈ X.Theta (scalOfP B hinj EX p w wL wF nT) w wL wF nT}

omit [NumberField K] in

def cuspRep (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) {P : Type} [Group P] (ρ : Representation B.KO P (B.Cusp j w)) :
    Representation K P (Fin n → K) := repCoord z ρ

omit [NumberField K] in
theorem cuspRep_tmul (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) {P : Type} [Group P]
    (ρ : Representation B.KO P (B.Cusp j w)) (g : P) (F : B.Cusp j w) :
    cuspRep B z ρ g (z.symm (1 ⊗ₜ F)) = z.symm (1 ⊗ₜ ρ g F) := by
  change z.symm ((ρ g).baseChange K (z (z.symm _))) = _
  rw [LinearEquiv.apply_symm_apply, LinearMap.baseChange_tmul]

omit [NumberField K] in

theorem exists_cuspRep_of_injective (f : B.Cusp j w →ₗ[B.KO] (Fin n → K)) (hf : Function.Injective f) {P : Type} [Group P]
    (σ : Representation K P (Fin n → K)) (a : P → B.Cusp j w → B.Cusp j w) (ha : ∀ g F, f (a g F) = σ g (f F)) :
    ∃ ρ : Representation B.KO P (B.Cusp j w), ∀ g F, ρ g F = a g F := by
  refine ⟨{ toFun := fun g =>
              { toFun := a g
                map_add' := fun F F' => hf (by rw [map_add, ha, ha, ha, map_add, map_add])
                map_smul' := fun c F => hf ?_ }
            map_one' := LinearMap.ext fun F => hf ?_
            map_mul' := fun g g' => LinearMap.ext fun F => hf ?_ }, fun _ _ => rfl⟩
  · rw [RingHom.id_apply, map_smul, ha, ha, map_smul, LinearMap.map_smul_of_tower]
  · change f (a 1 F) = f F
    rw [ha, map_one, Module.End.one_apply]
  · change f (a (g * g') F) = f (a g (a g' F))
    rw [ha, ha, ha, map_mul, Module.End.mul_apply]

end Cusp

variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

instance RunData.algFull (r : RunData T.J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst

def toFormsEquiv (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (i : Fin D.R.m) {n : ℕ}
    (z : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) :
    (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL) :=
  LinearEquiv.ofBijective (toForms h fw i z) (toForms_bijective h fw i z)

theorem toForms_symm (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (i : Fin D.R.m) {n : ℕ}
    (z : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((i : ℕ) + 1) (κ i))
    (x : Fin (R.nW i) → D.what₂.LL) : toForms h fw i z ((toFormsEquiv h fw i z).symm x) = x :=
  (toFormsEquiv h fw i z).apply_symm_apply x

theorem exists_toForms_eq_id (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (i : Fin D.R.m) :
    ∃ z : (Fin (R.nW i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), ∀ x, toForms h fw i z x = x := by
  obtain ⟨m, b, -, h1, h2, h3, h4⟩ := fw.ks i
  have hb := cusp_liftBaseChange_bijective (recB h.toLawsCore) (cuspTo h fw i) (cutTo_spec fw i).1 b h1
    (h2.trans (cutTo_spec fw i).2.symm) h3 h4
  exact ⟨(LinearEquiv.ofBijective _ hb).symm, fun x => (LinearEquiv.ofBijective _ hb).apply_symm_apply x⟩

theorem ActionPin.exists_rep {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {i : Fin D.R.m}
    {ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)}
    (ha : ActionPin h fw i ℓ) {P : Type} [Group P] (inc : P →* G) :
    ∃ ρ : Representation (recB h.toLawsCore).KO P ((recB h.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)),
      IsLevAct T.toTop h ((i : ℕ) + 1) (κ i) (fun g => ℓ (inc g)) fun g F => ρ g F := by
  obtain ⟨a, h1, h2⟩ := ha
  obtain ⟨ρ, hρ⟩ := exists_cuspRep_of_injective (recB h.toLawsCore) (cuspTo h fw i) (cutTo_spec fw i).1
    ((R.FW i).ρ.comp inc) (fun g => a (inc g)) fun g F => h2 (inc g) F
  exact ⟨ρ, fun g F => (congrArg Subtype.val (hρ g F)).trans (h1 (inc g) F)⟩

section Tied

variable (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
  (r : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData T.J) (hr : ∀ v, LawsP (r v).full.toTop)
  (p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ)
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  (ι : Bs.J → Fin D.R.m) (wL wF : ∀ i, WeightFamilies.Wt D ((ι i : ℕ) + 1)) (nT : ℕ) (inc : P →* G)
  (ℓ : ∀ i, G → (LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l))
  (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ)
  (ρ : ∀ i, Representation (recB h.toLawsCore).KO P ((recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))))
  (O : OnObj S P oc)
  (z : ∀ i, (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)))

def goodCoord (i : Fin D.R.m) {n : ℕ}
    (z : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) :
    (Fin n → D.what₂.LL) →ₗ[D.what₂.LL] (Fin n → D.what₂.LL) :=
  (toFormsEquiv h fw i z).symm.toLinearMap ∘ₗ (R.FW i).eOp (fun g => (idemOf A.X).coeff g) ∘ₗ toForms h fw i z

open Classical in

def classSumCoord (i : Fin D.R.m) {n : ℕ}
    (z : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((i : ℕ) + 1) (κ i))
    (t : T0) (c : ℂ) : (Fin (srcDim A i t U ψ) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin n → D.what₂.LL) :=
  if H : ClassSumRational R i t U ψ c then (toFormsEquiv h fw i z).symm.toLinearMap ∘ₗ H.choose else 0

theorem isClassSum_classSumCoord (i : Fin D.R.m) {n : ℕ}
    (z : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((i : ℕ) + 1) (κ i))
    (t : T0) (c : ℂ) (H : ClassSumRational R i t U ψ c) :
    IsClassSum R i t U ψ c (toForms h fw i z ∘ₗ classSumCoord h fw U ψ i z t c) := fun x =>
  have e : classSumCoord h fw U ψ i z t c = (toFormsEquiv h fw i z).symm.toLinearMap ∘ₗ H.choose := dif_pos H
  (congrArg (adForm R i) ((congrArg (toForms h fw i z) (LinearMap.congr_fun e x)).trans
    (toForms_symm h fw i z (H.choose x)))).trans (H.choose_spec x)

def objectActionInstance : OnObj S P oc :=
  { O with
    ρ := fun i => cuspRep (recB h.toLawsCore) (z i) (ρ i)
    U := U.comap inc
    ψ := charInt inc U ψ
    e := fun i => goodCoord h fw (ι i) (z i)
    V₀ := fun i => LinearMap.range (goodCoord h fw (ι i) (z i))
    Ms := fun i => supSpan (recB h.toLawsCore) (z i)
    Th := fun v i => scaledSpan (recB h.toLawsCore) (recPJ (hr v) ((ι i : ℕ) + 1) (inR_succ (ι i))) hinj EX (p v) (wL i) (wF i)
      nT (z i)
    ThK := fun v i => shortSpan (recB h.toLawsCore) (recPJ (hr v) ((ι i : ℕ) + 1) (inR_succ (ι i))) (z i)
    σ := fun _ i => algebraMap (recB h.toLawsCore).KO D.what₂.LL
      (sigRec (recB h.toLawsCore) hinj EX (κ (ι i)) (wL i) (wF i) nT : 𝓞 (recB h.toLawsCore).KO)
    Th0 := fun v i => thetaEig (hr v) ((ι i : ℕ) + 1) (κ (ι i)) (z i) (U.comap inc) (charInt inc U ψ) fun g => ℓ i (inc g)
    ThJ := fun v i => (thetaBase R (ι i) U ψ (ph v i) v (p v)).comap
      ((toForms h fw (ι i) (z i)).restrictScalars (𝓞 D.what₂.LL))
    X₃ := fun v i => ((thetaTuple R (ι i) U ψ (ph v i) (R.mu v)).comap
      ((toForms h fw (ι i) (z i)).restrictScalars (𝓞 D.what₂.LL))).map
        ((goodCoord h fw (ι i) (z i)).restrictScalars (𝓞 D.what₂.LL))
    nX := fun v i => srcDim A (ι i) (R.mu v) U ψ
    θ' := fun v i => classSumCoord h fw U ψ (ι i) (z i) (R.mu v) (ph v i)
    eX := fun v i => ((A.MtCSD (ι i) (R.mu v)).lvlOp (A.leftGroupActionLift (ι i) (R.mu v)) U ψ (idemOf A.X)).mulVecLin
    pr := fun v i => orthProj ((A.MtCSD (ι i) (R.mu v)).lvlH (A.leftGroupActionLift (ι i) (R.mu v)) U ψ)
      (perpOf ((A.MtCSD (ι i) (R.mu v)).lvlH (A.leftGroupActionLift (ι i) (R.mu v)) U ψ)
        (LinearMap.ker (classSumCoord h fw U ψ (ι i) (z i) (R.mu v) (ph v i))))
    Mt := fun v i => (A.MtCSD (ι i) (R.mu v)).lvlNab (A.leftGroupActionLift (ι i) (R.mu v)) U ψ }

theorem onTie_tiedObj
    (hρ : ∀ i, IsLevAct T.toTop h ((ι i : ℕ) + 1) (κ (ι i)) (fun g => ℓ i (inc g)) fun g F => ρ i g F)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Bs.J) :
    OnTie (T := (r v).full) (inst := inst) (R := R) (hr v) fw hinj EX (p v) (ι i) (wL i) (wF i) nT
      (objectActionInstance h fw hinj EX r hr p ι wL wF nT inc ℓ U ψ ph ρ O z) v i (z i) (fun g F => ρ i g F) inc (ℓ i) U ψ (ph v i)
      (LinearEquiv.refl _ _) where
  Ms_eq := rfl
  rho_eq := cuspRep_tmul (recB h.toLawsCore) (z i) (ρ i)
  Th_eq := rfl
  σ_eq := rfl
  ThK_eq := rfl
  act_eq := hρ i
  U_eq := rfl
  ψ_eq := charInt_coe inc U ψ
  e_eq := LinearMap.ext fun _ => toForms_symm h fw (ι i) (z i) _
  V₀_eq := rfl
  Th0_eq := rfl
  ThJ_eq := rfl
  X₃_eq := rfl
  Mt_eq := rfl
  θ'_eq H := isClassSum_classSumCoord h fw U ψ (ι i) (z i) (R.mu v) (ph v i) H
  eX_eq := rfl
  pr_eq := by
    change orthProj _ (perpOf _ (LinearMap.ker _)) = orthProj _ (perpOf _ ((LinearMap.ker _).map LinearMap.id))
    rw [Submodule.map_id]
    rfl

theorem tiedObj_keeps :
    let O' := objectActionInstance h fw hinj EX r hr p ι wL wF nT inc ℓ U ψ ph ρ O z
    O'.nZ = O.nZ ∧ O'.φ = O.φ ∧ O'.Th1 = O.Th1 ∧ O'.a = O.a ∧ O'.E = O.E ∧ O'.r1 = O.r1 ∧ O'.r2 = O.r2 ∧ O'.pde = O.pde ∧
      O'.ε0 = O.ε0 ∧ O'.nnK = O.nnK ∧ O'.Jp = O.Jp :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Tied

def blankObj (D : D7) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst)
    (n : Bs.J → ℕ) : OnObj S P oc where
  nZ := n
  ρ _ := 1
  U := ⊥
  ψ := 1
  V₀ _ := ⊥
  e _ := 0
  Ms _ := ⊥
  φ _ := 0
  Th1 _ _ := ⊥
  Th _ _ := ⊥
  ThK _ _ := ⊥
  Th0 _ _ := ⊥
  ThJ _ _ := ⊥
  X₃ _ _ := ⊥
  σ := 0
  a := 0
  E := 0
  r1 := 0
  r2 := 0
  pde := D.host.pde
  ε0 := 0
  nX := 0
  θ' _ _ := 0
  eX _ _ := 0
  pr _ _ := 0
  Mt _ _ := ⊥
  nnK := 0
  Jp := 0
  k := D.R.k
  m := D.R.m
  f := D.R.f
  bp := 0
  Sc := 0
  eta := 0
  T := 0
  DF := 0
  X2 := 0
  x := 0
  eps := 0
  vd := 0
  rr := D.R.r
  de2 := 0
  Nc := 0
  wt := 0
  th := 0
  ad := 0
  T2 := D.host.T2.card
  g1 := D.host.g 0
  g2 := D.host.g 1
  q1 := D.host.q
  dd := D.host.d
  sm := D.host.small

section Exists

variable (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
  (r : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData T.J) (hr : ∀ v, LawsP (r v).full.toTop)
  (p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ)
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst)
  (ι : Bs.J → Fin D.R.m) (wL wF : ∀ i, WeightFamilies.Wt D ((ι i : ℕ) + 1)) (nT : ℕ) (inc : P →* G)

def EquivariantLatticeCharacterDatumExists
    (ℓ : ∀ i, G → (LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l))
    (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ) : Prop :=
  ∃ (O : OnObj S P oc) (z : ∀ i, (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)))
    (act : ∀ i, P → (recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)) → (recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)))
    (y : ∀ v i, (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A (ι i) (R.mu v) U ψ) → D.what₂.LL)),
    O.pde = D.host.pde ∧ (∀ i, O.nZ i = R.nW (ι i)) ∧
      ∀ v i, OnTie (T := (r v).full) (inst := inst) (R := R) (hr v) fw hinj EX (p v) (ι i) (wL i) (wF i) nT O v i (z i) (act i)
        inc (ℓ i) U ψ (ph v i) (y v i)

theorem tiedRecordExists_of_rep
    (ℓ : ∀ i, G → (LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l))
    (hρ : ∀ i, ∃ ρ : Representation (recB h.toLawsCore).KO P ((recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))),
      IsLevAct T.toTop h ((ι i : ℕ) + 1) (κ (ι i)) (fun g => ℓ i (inc g)) fun g F => ρ g F)
    (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ) :
    EquivariantLatticeCharacterDatumExists h fw hinj EX r hr p S P oc ι wL wF nT inc ℓ U ψ ph := by
  choose ρ hρ using hρ
  choose z _ using fun i => exists_toForms_eq_id h fw (ι i)
  exact ⟨objectActionInstance h fw hinj EX r hr p ι wL wF nT inc ℓ U ψ ph ρ (blankObj D S P oc fun i => R.nW (ι i)) z, z,
    fun i g F => ρ i g F, fun _ _ => LinearEquiv.refl _ _, rfl, fun _ => rfl,
    onTie_tiedObj h fw hinj EX r hr p ι wL wF nT inc ℓ U ψ ph ρ (blankObj D S P oc fun i => R.nW (ι i)) z hρ⟩

theorem tiedRecordExists_of_actionPin
    (ℓ : ∀ i, G → (LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l))
    (ha : ∀ i, ActionPin h fw (ι i) (ℓ i))
    (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ) :
    EquivariantLatticeCharacterDatumExists h fw hinj EX r hr p S P oc ι wL wF nT inc ℓ U ψ ph :=
  tiedRecordExists_of_rep h fw hinj EX r hr p S P oc ι wL wF nT inc ℓ (fun i => (ha i).exists_rep inc) U ψ ph

theorem exists_tied_record
    (ℓ : ∀ i, G →* (LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l))
    (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ) :
    ∃ (O : OnObj S P oc) (z : ∀ i, (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
        D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)))
      (act : ∀ i, P → (recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)) → (recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)))
      (y : ∀ v i, (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A (ι i) (R.mu v) U ψ) → D.what₂.LL)),
      O.pde = D.host.pde ∧ (∀ i, O.nZ i = R.nW (ι i)) ∧
        ∀ v i, OnTie (T := (r v).full) (inst := inst) (R := R) (hr v) fw hinj EX (p v) (ι i) (wL i) (wF i) nT O v i (z i) (act i)
          inc (fun g => ℓ i g) U ψ (ph v i) (y v i) :=
  tiedRecordExists_of_rep h fw hinj EX r hr p S P oc ι wL wF nT inc (fun i g => ℓ i g)
    (fun i => exists_rep_isLevAct D T.toTop h _ (inR_succ (ι i)) (κ (ι i)) P ((ℓ i).comp inc)) U ψ ph

theorem exists_tied_record_one_run
    (ℓ : ∀ i, G →* (LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l))
    (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ) :
    ∃ (O : OnObj S P oc) (z : ∀ i, (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
        D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)))
      (act : ∀ i, P → (recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)) → (recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)))
      (y : ∀ v i, (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A (ι i) (R.mu v) U ψ) → D.what₂.LL)),
      O.pde = D.host.pde ∧ (∀ i, O.nZ i = R.nW (ι i)) ∧
        ∀ v i, OnTie h fw hinj EX (p v) (ι i) (wL i) (wF i) nT O v i (z i) (act i) inc (fun g => ℓ i g) U ψ (ph v i) (y v i) :=
  exists_tied_record h fw hinj EX (fun _ => RunData.ofFull T) (fun _ => h) p S P oc ι wL wF nT inc ℓ U ψ ph

end Exists

end GlobalTheory.OnTies
