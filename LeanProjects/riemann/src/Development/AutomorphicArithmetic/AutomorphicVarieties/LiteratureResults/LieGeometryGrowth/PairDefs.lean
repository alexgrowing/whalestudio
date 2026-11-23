import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg

noncomputable section

open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL

namespace UpperTheory.V.Lit.Geo.Pf

section Defs

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

structure CInv (F : GA E a → ℂ) : Prop where
  cont : Continuous F
  left : ∀ γ g, F (ratGL E a γ * g) = F g
  centre : ∀ t g, F (splitCentre E a t * g) = F g

structure SInv (φ : Sm E a) : Prop where
  left : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g
  centre : ∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g
  level : IsOpen {k | act (.fin k) φ = φ}

def Cs {M : Type} [Zero M] (F : GA E a → M) : Prop := ∃ R : ℝ, ∀ g, R < qht g → F g = 0

def QInt (μ : Measure (GA E a)) (F : GA E a → ℂ) : Prop :=
  Integrable (fun x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a) => F x.out) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)

def qint (μ : Measure (GA E a)) (F : GA E a → ℂ) : ℂ :=
  ∫ x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a), F x.out ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)

def TwInv (χ : HChar E) {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Prop := ∀ j, SInv (mulChi a χ (cmp j m))

def pt (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) : ℂ :=
  (‖((chiDet a χ g : ℂˣ) : ℂ)‖ ^ 2 : ℝ) * (star (ev x g) ⬝ᵥ G *ᵥ ev y g)

theorem cmp_ev {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : (cmp j m).1 g = ev m g j := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

theorem ptIp_eq {Ξ : AlgRep E a} {q : ℕ} (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) {n : ℕ} (e : Fin n → Herm E a)
    (α β : Co Ξ q) (g : GA E a) :
    ptIp χ G e α β g = ∑ I : Fin q → Fin n, pt χ G (α fun i => e (I i)) (β fun i => e (I i)) g := by
  simp only [ptIp, pt, Finset.mul_sum]

theorem CInv.sum {ι : Type} (s : Finset ι) {F : ι → GA E a → ℂ} (h : ∀ i, CInv (F i)) : CInv fun g => ∑ i ∈ s, F i g :=
  ⟨continuous_finset_sum _ fun i _ => (h i).cont, fun γ g => Finset.sum_congr rfl fun i _ => (h i).left γ g,
    fun t g => Finset.sum_congr rfl fun i _ => (h i).centre t g⟩

theorem cs_pt_left (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) {x : Sm E a ⊗[ℂ] (Fin d → ℂ)} (y : Sm E a ⊗[ℂ] (Fin d → ℂ))
    (h : Cs (ev x)) : Cs (pt χ G x y) :=
  h.imp fun _ hR g hg => by simp [pt, hR g hg]

theorem cs_pt_right (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) {y : Sm E a ⊗[ℂ] (Fin d → ℂ)}
    (h : Cs (ev y)) : Cs (pt χ G x y) :=
  h.imp fun _ hR g hg => by simp [pt, hR g hg]

end Defs

def InvLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), SInv φ →
    CInv φ.1 ∧ ∀ X : Lie E a, SInv (lie E a X φ)

def BddInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (F : GA E a → ℂ), CInv F → (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → QInt μ F ∧ GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ F

def CsBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), CInv F →
    (Cs F ∨ ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖F g.1‖ ≤ C) → ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C

def CsLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (X : Lie E a), Cs φ.1 → Cs (lie E a X φ).1

def ProdEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ ψ : Sm E a), ∃ θ : Sm E a,
    (∀ g, θ.1 g = starRingEnd ℂ (φ.1 g) * ψ.1 g) ∧
    ∀ (X : Lie E a) g, (lie E a X θ).1 g =
      starRingEnd ℂ ((lie E a X φ).1 g) * ψ.1 g + starRingEnd ℂ (φ.1 g) * (lie E a X ψ).1 g

def StokesFn : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (θ : Sm E a) (X : Lie E a), SInv θ → Cs θ.1 → qint μ (lie E a X θ).1 = 0

def LevInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E), HasOne Ξ r → IsTw (a := a) r χ →
    ∀ (q : ℕ) (α : Co Ξ q), IsLev U Ξ α → ∀ X, TwInv χ (α X)

def PtInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (χ : HChar E) (d : ℕ) (G : Matrix (Fin d) (Fin d) ℂ)
    (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)),
    (∀ g, pt χ G x y g = ∑ i, ∑ j, G i j *
      (starRingEnd ℂ ((mulChi a χ (cmp i x)).1 g) * (mulChi a χ (cmp j y)).1 g)) ∧
    ((TwInv χ x → TwInv χ y → CInv (pt χ G x y)) ∧
      ∀ θ : Sm E a, (∀ g, θ.1 g = pt χ G x y g) → TwInv χ x → TwInv χ y → SInv θ)

def TwLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E),
    IsTw (a := a) r χ → ∀ (X : Lie E a) (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), TwInv χ x →
      TwInv χ (smLie Ξ X x) ∧ TwInv χ (smAdj Ξ r X x)

def CsTens : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (X : Lie E a)
    (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), Cs (ev x) → Cs (ev (smLie Ξ X x)) ∧ Cs (ev (smAdj Ξ r X x))

def PtDiv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsTw (a := a) r χ → IsAdm Ξ G → ∀ x y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ),
    ∃ θ : Sm E a, (∀ g, θ.1 g = pt χ G x y g) ∧ ∀ (X : Herm E a) g,
      (lie E a (toL X.1) θ).1 g = pt χ G x (smLie Ξ (toL X.1) y) g - pt χ G (smAdj Ξ r (toL X.1) x) y g

def AdjInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsTw (a := a) r χ → IsAdm Ξ G →
    ∀ (X : Herm E a) (x y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), TwInv χ x → TwInv χ y → Cs (ev x) ∨ Cs (ev y) →
      QInt μ (pt χ G x (smLie Ξ (toL X.1) y)) ∧ QInt μ (pt χ G (smAdj Ξ r (toL X.1) x) y) ∧
        qint μ (pt χ G x (smLie Ξ (toL X.1) y)) = qint μ (pt χ G (smAdj Ξ r (toL X.1) x) y)

def PtD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a) (q : ℕ)
    (L : Lie E a →ₗ[ℝ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (β : Co Ξ (q + 1)) (η : Co Ξ q) (g : GA E a),
    ptIp χ G e β (dCo L η) g = ((q : ℂ) + 1) * ∑ J : Fin q → Fin n, ∑ j,
        pt χ G (β (Matrix.vecCons (e j) fun i => e (J i))) (L (toL (e j).1) (η fun i => e (J i))) g ∧
      ptIp χ G e (del L e β) η g = ∑ J : Fin q → Fin n, ∑ j,
        pt χ G (L (toL (e j).1) (β (Matrix.vecCons (e j) fun i => e (J i)))) (η fun i => e (J i)) g

def ChiOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (χ : HChar E) (s : ℝ), χ.IsAbsPow s →
    ∀ g : KernelIndexFullLattice.G1 E a, ‖((chiDet a χ g.1 : ℂˣ) : ℂ)‖ = 1

def RapidBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (χ : HChar E) (s : ℝ), χ.IsAbsPow s →
    ∀ (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a) (q : ℕ) (α β : Co Ξ q), Rapid α → Moderate β →
      ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖ptIp χ G e α β g.1‖ ≤ C

def ZeroInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (F : GA E a → ℂ), CInv F → (∀ g, ∃ t : ℝ, 0 ≤ t ∧ F g = t) → QInt μ F → qint μ F = 0 → ∀ g, F g = 0

def PtPos : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsAdm Ξ G → ∀ (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (q : ℕ) (α : Co Ξ q),
    (∀ g, ∃ t : ℝ, 0 ≤ t ∧ ptIp χ G e α α g = t) ∧ ((∀ g, ptIp χ G e α α g = 0) → α = 0)

theorem pairFacts_of_steps (h1 : BddInt) (h2 : CsBdd) (h3 : LevInv) (h4 : PtInv) (h5 : AdjInt) (h6 : PtD) (h7 : RapidBdd)
    (h8 : ZeroInt) (h9 : PtPos) : PairFacts := by
  intro E _ _ _ a ha μ _ U hU Ξ r χ G n e hD q
  have hv := h3 E a ha U hU Ξ r χ hD.one hD.tw
  have hc : ∀ α β : Co Ξ q, IsLev U Ξ α → IsLev U Ξ β → CInv (ptIp χ G e α β) := fun α β hα hβ => by
    rw [show ptIp χ G e α β = _ from funext (ptIp_eq χ G e α β)]
    exact CInv.sum _ fun I => (h4 E a χ _ G _ _).2.1 (hv q α hα _) (hv q β hβ _)
  refine ⟨fun α β hα hβ hr hm => ?_, fun α β hα hβ hs => ⟨?_, ?_⟩, fun α hα hi h0 => ?_, fun β η hβ hη hs => ?_⟩
  · obtain ⟨s, hs⟩ := hD.tw.1
    exact (h1 E a μ _ (hc α β hα hβ) (h2 E a _ (hc α β hα hβ) (.inr (h7 E a Ξ χ s hs G n e q α β hr hm)))).1
  · refine (h1 E a μ _ (hc α β hα hβ) (h2 E a _ (hc α β hα hβ) (.inl ?_))).1
    exact hs.imp fun R hR g hg => by simp [ptIp, hR _ g hg]
  · refine (h1 E a μ _ (hc β α hβ hα) (h2 E a _ (hc β α hβ hα) (.inl ?_))).1
    exact hs.imp fun R hR g hg => by simp [ptIp, hR _ g hg]
  · have hp := h9 E a Ξ χ G hD.adm n e hD.frame q α
    exact hp.2 (h8 E a μ _ (hc α α hα hα) hp.1 hi h0)
  · have hA := fun (J : Fin q → Fin n) (j : Fin n) => h5 E a μ Ξ r χ G hD.tw hD.adm (e j)
      (β (Matrix.vecCons (e j) fun i => e (J i))) (η fun i => e (J i)) (hv _ β hβ _) (hv _ η hη _)
      (hs.imp (fun h => h.imp fun R hR g hg => hR _ g hg) fun h => h.imp fun R hR g hg => hR _ g hg)
    simp only [pair, (h6 E a Ξ χ G n e q (smLie Ξ) β η _).1, (h6 E a Ξ χ G n e q (smAdj Ξ r) β η _).2]
    rw [integral_const_mul, integral_finset_sum _ fun J _ => integrable_finset_sum _ fun j _ => (hA J j).1,
      integral_finset_sum _ fun J _ => integrable_finset_sum _ fun j _ => (hA J j).2.1]
    congr 1
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [integral_finset_sum _ fun j _ => (hA J j).1, integral_finset_sum _ fun j _ => (hA J j).2.1]
    exact Finset.sum_congr rfl fun j _ => (hA J j).2.2

end UpperTheory.V.Lit.Geo.Pf
