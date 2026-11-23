import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumRepDeRhamIffAndMultiplicityAdd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.Pst.SumOneField

open Module TensorProduct GlobalTheory.Pst.DpstMap

section FrobSS

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem isFrobSS_sum {ρ₁ : Weil h → End ℂ V} {N₁ : End ℂ V} {a : WDRep h V}
    {ρ₂ : Weil h → End ℂ V'} {N₂ : End ℂ V'} {b : WDRep h V'}
    (ha : IsFrobSS ρ₁ N₁ a) (hb : IsFrobSS ρ₂ N₂ b) :
    IsFrobSS (fun g => (ρ₁ g).prodMap (ρ₂ g)) (N₁.prodMap N₂) (a.sum b) := by
  refine ⟨by rw [WDRep.sum_N, ha.1, hb.1], fun g => ?_⟩
  obtain ⟨c1, n1⟩ := ha.2 g
  obtain ⟨c2, n2⟩ := hb.2 g
  let R := LinearMap.prodMapRingHom ℂ V V'
  have e1 : (a.sum b).ρ g = R (a.ρ g, b.ρ g) := rfl
  have e2 : (ρ₁ g).prodMap (ρ₂ g) = R (ρ₁ g, ρ₂ g) := rfl
  show Commute ((a.sum b).ρ g) ((ρ₁ g).prodMap (ρ₂ g)) ∧ IsNilpotent ((ρ₁ g).prodMap (ρ₂ g) - (a.sum b).ρ g)
  rw [e1, e2]
  have hc : Commute ((a.ρ g, b.ρ g) : End ℂ V × End ℂ V') (ρ₁ g, ρ₂ g) := Prod.ext c1.eq c2.eq
  refine ⟨hc.map R, ?_⟩
  rw [← map_sub]
  obtain ⟨m, hm⟩ := n1
  obtain ⟨n, hn⟩ := n2
  refine IsNilpotent.map ⟨m + n, Prod.ext ?_ ?_⟩ R
  · simp [pow_add, hm]
  · simp [pow_add, hn]

end FrobSS

section Tens

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V V' V'' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
  [AddCommGroup V''] [Module LL V''] [Module ℚ_[l] V''] [IsScalarTower ℚ_[l] LL V'']

theorem tensV_comp (f : V →ₗ[LL] V') (g : V' →ₗ[LL] V'') (z : V ⊗[ℚ_[l]] Bst P) :
    tensV P g (tensV P f z) = tensV P (g ∘ₗ f) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensV_id (z : V ⊗[ℚ_[l]] Bst P) : tensV P (LinearMap.id : V →ₗ[LL] V) z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensV_zero (z : V ⊗[ℚ_[l]] Bst P) : tensV P (0 : V →ₗ[LL] V') z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem tensV_add (f g : V →ₗ[LL] V') (z : V ⊗[ℚ_[l]] Bst P) :
    tensV P (f + g) z = tensV P f z + tensV P g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [add_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]; abel

end Tens

section Split

variable (k : Type) [Field k] (a b : ℕ)

def pr₁ : (Fin (a + b) → k) →ₗ[k] (Fin a → k) :=
  LinearMap.fst k _ _ ∘ₗ (GlobalTheory.DirectSumLocal.splitEquiv k a b).toLinearMap

def pr₂ : (Fin (a + b) → k) →ₗ[k] (Fin b → k) :=
  LinearMap.snd k _ _ ∘ₗ (GlobalTheory.DirectSumLocal.splitEquiv k a b).toLinearMap

def in₁ : (Fin a → k) →ₗ[k] (Fin (a + b) → k) :=
  (GlobalTheory.DirectSumLocal.splitEquiv k a b).symm.toLinearMap ∘ₗ LinearMap.inl k _ _

def in₂ : (Fin b → k) →ₗ[k] (Fin (a + b) → k) :=
  (GlobalTheory.DirectSumLocal.splitEquiv k a b).symm.toLinearMap ∘ₗ LinearMap.inr k _ _

theorem pr₁_in₁ : pr₁ k a b ∘ₗ in₁ k a b = LinearMap.id := by ext v <;> simp [pr₁, in₁]
theorem pr₂_in₁ : pr₂ k a b ∘ₗ in₁ k a b = 0 := by ext v <;> simp [pr₂, in₁]
theorem pr₁_in₂ : pr₁ k a b ∘ₗ in₂ k a b = 0 := by ext v <;> simp [pr₁, in₂]
theorem pr₂_in₂ : pr₂ k a b ∘ₗ in₂ k a b = LinearMap.id := by ext v <;> simp [pr₂, in₂]
theorem in_pr : in₁ k a b ∘ₗ pr₁ k a b + in₂ k a b ∘ₗ pr₂ k a b = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  simp only [pr₁, pr₂, in₁, in₂, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, ← map_add]
  apply (GlobalTheory.DirectSumLocal.splitEquiv k a b).injective
  simp

end Split

end GlobalTheory.Pst.SumOneField

namespace GlobalTheory.Pst.SumOneField

open Module TensorProduct GlobalTheory.Pst.DpstMap

section WdLin

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K LL : FinExt l}
  {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁]
  [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂]
  [AddCommGroup V₃] [Module ↥LL.1 V₃] [Module ℚ_[l] V₃] [IsScalarTower ℚ_[l] ↥LL.1 V₃]
  {r₁ : Representation ↥LL.1 ↥(GK K) V₁} {r₂ : Representation ↥LL.1 ↥(GK K) V₂}
  {r₃ : Representation ↥LL.1 ↥(GK K) V₃}

theorem wdLin_comp_eq_id {f : V₁ →ₗ[↥LL.1] V₂} {g : V₂ →ₗ[↥LL.1] V₁} (hf : ∀ x v, f (r₁ x v) = r₂ x (f v))
    (hg : ∀ x v, g (r₂ x v) = r₁ x (g v)) (hgf : g ∘ₗ f = LinearMap.id) :
    wdLin P ι hg ∘ₗ wdLin P ι hf = LinearMap.id :=
  LinearMap.ext_on_range (span_wdMk P ι r₁) fun x => congrArg (wdMk P ι r₁) (Subtype.ext
    ((tensV_comp P f g x.1).trans ((congrArg (fun k => tensV P k x.1) hgf).trans (tensV_id P x.1))))

theorem wdLin_comp_eq_zero {f : V₁ →ₗ[↥LL.1] V₂} {g : V₂ →ₗ[↥LL.1] V₃} (hf : ∀ x v, f (r₁ x v) = r₂ x (f v))
    (hg : ∀ x v, g (r₂ x v) = r₃ x (g v)) (hgf : g ∘ₗ f = 0) :
    wdLin P ι hg ∘ₗ wdLin P ι hf = 0 :=
  LinearMap.ext_on_range (span_wdMk P ι r₁) fun x => (congrArg (wdMk P ι r₃) (Subtype.ext
    ((tensV_comp P f g x.1).trans ((congrArg (fun k => tensV P k x.1) hgf).trans (tensV_zero P x.1))))).trans
      (wdMk_zero P ι r₃)

end WdLin

section Iso

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)

theorem isFrobSS_wdRep {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] (r : Representation ↥LL.1 ↥(GK Bw.Kw) V)
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P r)] :
    IsFrobSS (wdRho P ι Bw h hj r) (wdN P ι r) (wdRep P ι Bw h hj r) := by
  obtain ⟨u, hN, hu, -, hc, hr⟩ := wdRep_spec P ι Bw h hj r
  rw [← hN]
  exact isFrobSS_of_unipotent u hu hc hr

variable {LL : FinExt l} {a b : ℕ} (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) (Fin (a + b) → ↥LL.1))
  (ρ₁ : Representation ↥LL.1 ↥(GK Bw.Kw) (Fin a → ↥LL.1)) (ρ₂ : Representation ↥LL.1 ↥(GK Bw.Kw) (Fin b → ↥LL.1))
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₁)]
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₂)]

theorem wdRep_iso_sum
    (he : ∀ g v, GlobalTheory.DirectSumLocal.splitEquiv (↥LL.1) a b (ρ g v) =
      (ρ₁ g (GlobalTheory.DirectSumLocal.splitEquiv (↥LL.1) a b v).1, ρ₂ g (GlobalTheory.DirectSumLocal.splitEquiv (↥LL.1) a b v).2)) :
    (wdRep P ι Bw h hj ρ).Iso ((wdRep P ι Bw h hj ρ₁).sum (wdRep P ι Bw h hj ρ₂)) := by
  have hp₁ : ∀ g v, pr₁ (↥LL.1) a b (ρ g v) = ρ₁ g (pr₁ (↥LL.1) a b v) := fun g v => by
    simp only [pr₁, LinearMap.comp_apply, LinearEquiv.coe_coe, he, LinearMap.fst_apply]
  have hp₂ : ∀ g v, pr₂ (↥LL.1) a b (ρ g v) = ρ₂ g (pr₂ (↥LL.1) a b v) := fun g v => by
    simp only [pr₂, LinearMap.comp_apply, LinearEquiv.coe_coe, he, LinearMap.snd_apply]
  have hi₁ : ∀ g v, in₁ (↥LL.1) a b (ρ₁ g v) = ρ g (in₁ (↥LL.1) a b v) := fun g v => by
    apply (GlobalTheory.DirectSumLocal.splitEquiv (↥LL.1) a b).injective
    rw [he]; simp [in₁]
  have hi₂ : ∀ g v, in₂ (↥LL.1) a b (ρ₂ g v) = ρ g (in₂ (↥LL.1) a b v) := fun g v => by
    apply (GlobalTheory.DirectSumLocal.splitEquiv (↥LL.1) a b).injective
    rw [he]; simp [in₂]
  let Φ : WDSpace P ι ρ →ₗ[ℂ] WDSpace P ι ρ₁ × WDSpace P ι ρ₂ := (wdLin P ι hp₁).prod (wdLin P ι hp₂)
  let Ψ : WDSpace P ι ρ₁ × WDSpace P ι ρ₂ →ₗ[ℂ] WDSpace P ι ρ := (wdLin P ι hi₁).coprod (wdLin P ι hi₂)
  have hΨΦ : Ψ ∘ₗ Φ = LinearMap.id := LinearMap.ext_on_range (span_wdMk P ι ρ) fun x => by
    show wdLin P ι hi₁ (wdLin P ι hp₁ (wdMk P ι ρ x)) + wdLin P ι hi₂ (wdLin P ι hp₂ (wdMk P ι ρ x)) = wdMk P ι ρ x
    exact (wdMk_add P ι ρ _ _).symm.trans (congrArg (wdMk P ι ρ) (Subtype.ext
      ((Submodule.coe_add _ _).trans ((congrArg₂ (· + ·) (tensV_comp P (pr₁ (↥LL.1) a b) (in₁ (↥LL.1) a b) x.1)
      (tensV_comp P (pr₂ (↥LL.1) a b) (in₂ (↥LL.1) a b) x.1)).trans ((tensV_add P _ _ x.1).symm.trans
        ((congrArg (fun f => tensV P f x.1) (in_pr (↥LL.1) a b)).trans (tensV_id P x.1)))))))
  have c11 := wdLin_comp_eq_id P ι hi₁ hp₁ (pr₁_in₁ (↥LL.1) a b)
  have c22 := wdLin_comp_eq_id P ι hi₂ hp₂ (pr₂_in₂ (↥LL.1) a b)
  have c21 := wdLin_comp_eq_zero P ι hi₁ hp₂ (pr₂_in₁ (↥LL.1) a b)
  have c12 := wdLin_comp_eq_zero P ι hi₂ hp₁ (pr₁_in₂ (↥LL.1) a b)
  have hΦΨ : Φ ∘ₗ Ψ = LinearMap.id := LinearMap.ext fun y => Prod.ext
    (show wdLin P ι hp₁ (wdLin P ι hi₁ y.1 + wdLin P ι hi₂ y.2) = y.1 from
      ((LinearMap.map_add (wdLin P ι hp₁) _ _).trans (congrArg₂ (· + ·) (LinearMap.congr_fun c11 y.1)
        (LinearMap.congr_fun c12 y.2))).trans (add_zero y.1))
    (show wdLin P ι hp₂ (wdLin P ι hi₁ y.1 + wdLin P ι hi₂ y.2) = y.2 from
      ((LinearMap.map_add (wdLin P ι hp₂) _ _).trans (congrArg₂ (· + ·) (LinearMap.congr_fun c21 y.1)
        (LinearMap.congr_fun c22 y.2))).trans (zero_add y.2))
  let e : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι ρ₁ × WDSpace P ι ρ₂ := LinearEquiv.ofLinear Φ Ψ hΦΨ hΨΦ
  have hρe : ∀ σ y, e (wdRho P ι Bw h hj ρ σ y) =
      ((wdRho P ι Bw h hj ρ₁ σ).prodMap (wdRho P ι Bw h hj ρ₂ σ)) (e y) := fun σ y =>
    Prod.ext (wdLin_wdRho P ι Bw h hj hp₁ σ y) (wdLin_wdRho P ι Bw h hj hp₂ σ y)
  have hNe : ∀ y, e (wdN P ι ρ y) = ((wdN P ι ρ₁).prodMap (wdN P ι ρ₂)) (e y) := fun y =>
    Prod.ext (wdLin_wdN P ι hp₁ y) (wdLin_wdN P ι hp₂ y)
  have h0 := isFrobSS_wdRep P ι Bw h hj ρ
  have h12 := isFrobSS_sum (isFrobSS_wdRep P ι Bw h hj ρ₁) (isFrobSS_wdRep P ι Bw h hj ρ₂)
  exact IsFrobSS.iso h0 h12 e hρe hNe

end Iso

theorem wdPst_sumRep : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a b : ℕ} (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (s' : ↥(Dec (F := E) A) →* GL (Fin b) ↥L.1), IsPst P (Bw.repE L s) → IsPst P (Bw.repE L s') → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) → wdPst P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) = (wdPst P ι Bw h hj (Bw.repE L s)).lpSum (wdPst P ι Bw h hj (Bw.repE L s')) := by
  intro l _ P ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj L a b s s' hV₁ hV₂ hV
  haveI := hV₁.finite
  haveI := hV₂.finite
  haveI := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, wdPst_of_isPst ι Bw h hj hV₁, wdPst_of_isPst ι Bw h hj hV₂, WD.lpSum_mk]
  exact WD.sound (wdRep_iso_sum P ι Bw h hj _ _ _ fun g v => GlobalTheory.DirectSumLocal.splitEquiv_sumRep s s' _ v)

end GlobalTheory.Pst.SumOneField
