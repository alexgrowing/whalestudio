import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSecondBlockRestriction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LimV.BlockTy

section Abs

theorem mem_of_separating {X Y M : Type} [AddCommGroup M] [Module ℂ M] (W : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ W] (v : X → M) (e : Y → M →ₗ[ℂ] ℂ) (hsep : ∀ m, (∀ y, e y m = 0) → m = 0)
    (l : M →ₗ[ℂ] ℂ) (hW : ∀ y, (fun x => e y (v x)) ∈ W) : (fun x => l (v x)) ∈ W := by
  classical
  let ev : X → Module.Dual ℂ W := fun x => (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype
  let A : (X →₀ ℂ) →ₗ[ℂ] Module.Dual ℂ W := Finsupp.linearCombination ℂ ev
  let B : (X →₀ ℂ) →ₗ[ℂ] M := Finsupp.linearCombination ℂ v
  have hAB : ∀ y μ, e y (B μ) = A μ ⟨_, hW y⟩ := by
    intro y μ
    have : (e y) ∘ₗ B = (LinearMap.applyₗ (⟨_, hW y⟩ : W)) ∘ₗ A := by
      refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
      simp [A, B, ev]
    exact LinearMap.congr_fun this μ
  have hsurj : LinearMap.range A = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    obtain ⟨w, rfl⟩ := (Module.evalEquiv ℂ W).surjective f
    apply hf0
    have hw : w = 0 := by
      refine Subtype.ext (funext fun x => ?_)
      have h1 : A (Finsupp.single x 1) ∈ LinearMap.ker (Module.evalEquiv ℂ W w : Module.Dual ℂ (Module.Dual ℂ W)) :=
        hf ⟨_, rfl⟩
      rw [LinearMap.mem_ker] at h1
      simpa [A, ev] using h1
    rw [hw, map_zero]
  obtain ⟨A', hA'⟩ := A.exists_rightInverse_of_surjective hsurj
  let ξ : Module.Dual ℂ (Module.Dual ℂ W) := l ∘ₗ B ∘ₗ A'
  obtain ⟨w, hw⟩ := (Module.evalEquiv ℂ W).surjective ξ
  have hval : ∀ d : Module.Dual ℂ W, d w = l (B (A' d)) := fun d => by
    have := LinearMap.congr_fun hw d
    simpa [ξ] using this
  convert w.2 using 1
  funext x
  have h1 : A (Finsupp.single x 1 - A' (A (Finsupp.single x 1))) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact (LinearMap.congr_fun hA' _).symm
  have h2 : B (Finsupp.single x 1 - A' (A (Finsupp.single x 1))) = 0 := by
    refine hsep _ fun y => ?_
    rw [hAB, h1]
    rfl
  have h3 : B (Finsupp.single x 1) = v x := by simp [B]
  rw [map_sub, sub_eq_zero, h3] at h2
  have h4 : A (Finsupp.single x 1) w = w.1 x := by simp [A, ev]
  rw [h2, ← hval, h4]

variable {G : Type} [Monoid G]

def coreL (W : Submodule ℂ (G → ℂ)) : Submodule ℂ (G → ℂ) :=
  ⨅ a : G, W.comap (LinearMap.funLeft ℂ ℂ fun x => a * x)

theorem mem_coreL {W : Submodule ℂ (G → ℂ)} {w : G → ℂ} : w ∈ coreL W ↔ ∀ a, (fun x => w (a * x)) ∈ W := by
  simp only [coreL, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem coreL_le (W : Submodule ℂ (G → ℂ)) : coreL W ≤ W := fun w hw => by
  simpa using mem_coreL.1 hw 1

def ltr (W : Submodule ℂ (G → ℂ)) (a : G) : coreL W →ₗ[ℂ] coreL W where
  toFun w := ⟨fun x => w.1 (a * x), mem_coreL.2 fun b => by
    simpa only [mul_assoc] using mem_coreL.1 w.2 (a * b)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coefB (W : Submodule ℂ (G → ℂ)) : Module.Dual ℂ (coreL W) →ₗ[ℂ] coreL W →ₗ[ℂ] (G → ℂ) :=
  LinearMap.mk₂ ℂ (fun l w x => l (ltr W x w))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun l w w' => funext fun x => by simp) (fun c l w => funext fun x => by simp)

def rs (W : Submodule ℂ (G → ℂ)) : Submodule ℂ (G → ℂ) := LinearMap.range (TensorProduct.lift (coefB W))

instance fd_rs (W : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ W] : FiniteDimensional ℂ (rs W) := by
  haveI : FiniteDimensional ℂ (coreL W) := Submodule.finiteDimensional_of_le (coreL_le W)
  exact LinearMap.finiteDimensional_range _

theorem mem_rs {W : Submodule ℂ (G → ℂ)} {w : G → ℂ} (hw : w ∈ coreL W) (k : G) : (fun x => w (x * k)) ∈ rs W := by
  refine ⟨((LinearMap.proj k : (G → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (coreL W).subtype) ⊗ₜ ⟨w, hw⟩, ?_⟩
  rw [TensorProduct.lift.tmul]
  rfl

theorem finite_sig {α : Type*} {P : ℕ → Prop} (hP : ∀ a b, P a → P b → a = b) (A : ∀ s, P s → Set α)
    (hA : ∀ s h, (A s h).Finite) : {x | ∃ s, ∃ h : P s, x ∈ A s h}.Finite := by
  by_cases hex : ∃ a, P a
  · obtain ⟨a, ha⟩ := hex
    refine (hA a ha).subset ?_
    rintro x ⟨s, h, hx⟩
    obtain rfl := hP _ _ h ha
    exact hx
  · refine Set.finite_empty.subset ?_
    rintro x ⟨s, h, -⟩
    exact hex ⟨s, h⟩

end Abs

section Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N r s : ℕ}

def resL (r s : ℕ) (W : Submodule ℂ (Kinf E (r + s) → ℂ)) : Submodule ℂ (Kinf E r → ℂ) :=
  (rs W).map (LinearMap.funLeft ℂ ℂ (Slice1.levK E r s))

def resR (r s : ℕ) (W : Submodule ℂ (Kinf E (r + s) → ℂ)) : Submodule ℂ (Kinf E s → ℂ) :=
  (rs W).map (LinearMap.funLeft ℂ ℂ (Slice2.levK E r s))

theorem fd_resL (W : Submodule ℂ (Kinf E (r + s) → ℂ)) [FiniteDimensional ℂ W] :
    FiniteDimensional ℂ (resL r s W) := by
  unfold resL
  infer_instance

theorem fd_resR (W : Submodule ℂ (Kinf E (r + s) → ℂ)) [FiniteDimensional ℂ W] :
    FiniteDimensional ℂ (resR r s W) := by
  unfold resR
  infer_instance

theorem translate_mem_coreL {W : Submodule ℂ (Kinf E N → ℂ)} {f : GA E N → ℂ}
    (hf : ∀ g, (fun k : Kinf E N => f (g * infGL E N (Unitary.toUnits k))) ∈ W) (g : GA E N) :
    (fun k : Kinf E N => f (g * infGL E N (Unitary.toUnits k))) ∈ coreL W := by
  refine mem_coreL.2 fun a => ?_
  simpa only [map_mul, mul_assoc] using hf (g * infGL E N (Unitary.toUnits a))

theorem type_transfer {W : Submodule ℂ (Kinf E N → ℂ)} [FiniteDimensional ℂ W] {φ : Sm E N}
    (hφ : ∀ g, (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) ∈ W) (f : Sm E N →ₗ[ℂ] Sm E N)
    (hf : ∀ k : Kinf E N, f (act (.cpt k) φ) = act (.cpt k) (f φ)) (g : GA E N) :
    (fun k : Kinf E N => (f φ).1 (g * infGL E N (Unitary.toUnits k))) ∈ W := by
  let e : GA E N → Sm E N →ₗ[ℂ] ℂ := fun y => (LinearMap.proj y : (GA E N → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (Sm E N).subtype
  have h := mem_of_separating W (fun k : Kinf E N => act (.cpt k) φ) e
    (fun m hm => Subtype.ext (funext hm)) (e g ∘ₗ f) hφ
  convert h using 2 with k
  exact (congrArg (fun ψ : Sm E N => ψ.1 g) (hf k)).symm

theorem cf_eq (k : Kinf E N) (t : GL (Fin N) (Af E)) :
    cf N k t = finGL E N t * infGL E N (Unitary.toUnits k) := by
  rw [cf, infGL_comm]

theorem slice_first {K : Subgroup (GL (Fin (r + s)) (Af E))} {W : Submodule ℂ (Kinf E (r + s) → ℂ)}
    {f : GA E (r + s) → ℂ} (hf : f ∈ typeF K W) (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) (y : GA E s) :
    (fun x : GA E r => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF (Slice1.levelOne s K t) (resL r s W) := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · have h := Slice1.lev_finGL_right g u y t (Unitary.toUnits k)
    have h' := hf.1 _ (Slice1.mem_levelOne.1 hu)
      (lev (Ad E) r s (g, y) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k))
    rw [← h] at h'
    simpa only [cf_eq, mul_assoc] using h'
  · refine ⟨_, mem_rs (translate_mem_coreL hf.2 (lev (Ad E) r s (g, y) * finGL E (r + s) t)) k, ?_⟩
    funext κ
    have h := Slice1.lev_infGL_right g (Unitary.toUnits κ) y t (Unitary.toUnits k)
    have e : lev (Cinf E) r s (Unitary.toUnits κ, 1) * Unitary.toUnits k =
        Unitary.toUnits (Slice1.levK E r s κ * k) := by
      rw [map_mul, Slice1.toUnits_levK]
    rw [e] at h
    simp only [LinearMap.funLeft_apply, cf_eq]
    rw [← h]
    simp only [mul_assoc]

theorem slice_second {K : Subgroup (GL (Fin (r + s)) (Af E))} {W : Submodule ℂ (Kinf E (r + s) → ℂ)}
    {f : GA E (r + s) → ℂ} (hf : f ∈ typeF K W) (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) (x : GA E r) :
    (fun y : GA E s => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF (SliceR.levelTwo K t) (resR r s W) := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · change f (lev (Ad E) r s (x, g * finGL E s u) * cf (r + s) k t) = f (lev (Ad E) r s (x, g) * cf (r + s) k t)
    rw [SliceR.lev_finGL_right]
    exact hf.1 _ (SliceR.mem_levelTwo.1 hu) _
  · refine ⟨_, mem_rs (translate_mem_coreL hf.2 (lev (Ad E) r s (x, g) * finGL E (r + s) t)) k, ?_⟩
    funext κ
    change f _ = f (lev (Ad E) r s (x, g * infGL E s (Unitary.toUnits κ)) * cf (r + s) k t)
    rw [SliceR.lev_infGL_right]

theorem hasType_of_tw {U : Submodule ℂ (Sm E N)} {z : ℂ} {K : Subgroup (GL (Fin N) (Af E))}
    {W : Submodule ℂ (Kinf E N → ℂ)} {F : Sm E N} (hF : F ∈ tw U z) (h0 : F ≠ 0) (hT : F.1 ∈ typeF K W) :
    PositivityTheory.Rg.BcB.SpectralAccumulation.HasType (K ⊓ KO E N) W U := by
  obtain ⟨χ, hχ, rfl⟩ := hF
  have hval : ∀ x, (mulChi N (Model.absC E z) χ).1 x = ((chiDet N (Model.absC E z) x : ℂˣ) : ℂ) * χ.1 x :=
    fun x => by rw [mulChi_apply, mul_comm]
  have hfin : ∀ g, ∀ u ∈ KO E N, chiDet N (Model.absC E z) (g * finGL E N u) = chiDet N (Model.absC E z) g := by
    intro g u hu
    have := chiDet_absC_cf N z (1 : Kinf E N) hu
    rw [cf, map_one, map_one, one_mul] at this
    rw [map_mul, this, mul_one]
  have hinf : ∀ g, ∀ k : Kinf E N, chiDet N (Model.absC E z) (g * infGL E N (Unitary.toUnits k)) =
      chiDet N (Model.absC E z) g := by
    intro g k
    have := chiDet_absC_cf N z k (one_mem (KO E N))
    rw [cf, map_one, mul_one] at this
    rw [map_mul, this, mul_one]
  refine ⟨χ, hχ, fun h => h0 (by rw [LinearEquiv.coe_coe, h, map_zero]), fun u hu g => ?_, fun g => ?_⟩
  · have h1 := hT.1 u hu.1 g
    simp only [LinearEquiv.coe_coe] at h1
    rw [hval, hval, hfin g u hu.2] at h1
    exact mul_left_cancel₀ (Units.ne_zero _) h1
  · have h1 := W.smul_mem (((chiDet N (Model.absC E z) g : ℂˣ) : ℂ))⁻¹ (hT.2 g)
    convert h1 using 1
    funext k
    simp only [LinearEquiv.coe_coe, Pi.smul_apply, smul_eq_mul]
    rw [hval, hinf, inv_mul_cancel_left₀ (Units.ne_zero _)]

theorem blocks {K : Subgroup (GL (Fin (r + s)) (Af E))} {W : Submodule ℂ (Kinf E (r + s) → ℂ)}
    [FiniteDimensional ℂ W] {T : Finset (GL (Fin (r + s)) (Af E))}
    (hT : ∀ g : GA E (r + s), ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (t : GL (Fin (r + s)) (Af E))
      (k : Kinf E (r + s)) (l : GL (Fin (r + s)) (Af E)), t ∈ T ∧ l ∈ K ∧
      g = unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l)
    {V : Submodule ℂ (Sm E (r + s))} {V₁ : Submodule ℂ (Sm E r)} {V₂ : Submodule ℂ (Sm E s)} {z₁ z₂ : ℂ}
    (hty : PositivityTheory.Rg.BcB.SpectralAccumulation.HasType K W V) (hemb : Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂))) :
    ∃ t ∈ T, PositivityTheory.Rg.BcB.SpectralAccumulation.HasType (Slice1.levelOne s K t ⊓ KO E r) (resL r s W) V₁ ∧
      PositivityTheory.Rg.BcB.SpectralAccumulation.HasType (SliceR.levelTwo K t ⊓ KO E s) (resR r s W) V₂ := by
  obtain ⟨φ, hφV, hφ0, hlev, hty⟩ := hty
  obtain ⟨f, hmem, hinj, heq⟩ := hemb
  have hG0 : f φ ≠ 0 := fun h => hφ0 (hinj φ hφV h)
  have hGlev : ∀ u ∈ K, ∀ g, (f φ).1 (g * finGL E (r + s) u) = (f φ).1 g := by
    intro u hu g
    have e : act (.fin u) φ = φ := Subtype.ext (funext fun x => hlev u hu x)
    have h1 := heq (.fin u) φ hφV
    rw [e] at h1
    exact (congrArg (fun ψ : Sm E (r + s) => ψ.1 g) h1).symm
  have hGf : (f φ).1 ∈ typeF K W := ⟨hGlev, type_transfer hty f fun k => heq (.cpt k) φ hφV⟩
  obtain ⟨hu, hs⟩ := hmem φ hφV
  obtain ⟨g₀, hg₀⟩ : ∃ g, (f φ).1 g ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hG0 (Subtype.ext (funext hc))
  obtain ⟨x, m, t, k, l, ht, hl, rfl⟩ := hT g₀
  have hne : (f φ).1 (lev (Ad E) r s m * cf (r + s) k t) ≠ 0 := by
    have e : unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l =
        unip x * (lev (Ad E) r s m * cf (r + s) k t) * finGL E (r + s) l := by
      rw [cf_eq]
      simp only [mul_assoc]
    rw [e, hGlev l hl, hu] at hg₀
    exact hg₀
  obtain ⟨n, ψ₁, ψ₂, h₁, h₂, hsum⟩ := ParabolicProjection.tensor_pair_finite_sum (hs k t)
  have hsum' : ∀ m', (f φ).1 (lev (Ad E) r s m' * cf (r + s) k t) = ∑ i, (ψ₁ i).1 m'.1 * (ψ₂ i).1 m'.2 := hsum
  have hne' : ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 ≠ 0 := hsum' m ▸ hne
  refine ⟨t, ht, ?_, ?_⟩
  · refine hasType_of_tw (F := ∑ i, (ψ₂ i).1 m.2 • ψ₁ i)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₁ i)) (ParabolicProjection.sum_left_ne hne') ?_
    convert slice_first hGf k t m.2 using 1
    funext y
    rw [hsum' (y, m.2)]
    simp [Submodule.coe_sum, Finset.sum_apply, mul_comm]
  · refine hasType_of_tw (F := ∑ i, (ψ₁ i).1 m.1 • ψ₂ i)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₂ i)) (ParabolicProjection.sum_right_ne hne') ?_
    convert slice_second hGf k t m.1 using 1
    funext y
    rw [hsum' (m.1, y)]
    simp [Submodule.coe_sum, Finset.sum_apply]

end Lin

theorem blockTypes : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.BlockTypes := by
  intro E _ _ _ N W hW
  have hu₁ : ∀ M : ℕ, ∀ a b, M + a = N → M + b = N → a = b := fun M a b h h' => by omega
  have hu₂ : ∀ M : ℕ, ∀ a b, a + M = N → b + M = N → a = b := fun M a b h h' => by omega
  refine ⟨fun M => {W' | ∃ s, ∃ h : M + s = N, W' ∈ ({resL M s (h ▸ W)} : Set (Submodule ℂ (Kinf E M → ℂ)))} ∪
    {W' | ∃ r, ∃ h : r + M = N, W' ∈ ({resR r M (h ▸ W)} : Set (Submodule ℂ (Kinf E M → ℂ)))}, fun M => ⟨?_, ?_⟩,
    fun K hK => ?_⟩
  · exact (finite_sig (hu₁ M) _ fun _ _ => Set.finite_singleton _).union
      (finite_sig (hu₂ M) _ fun _ _ => Set.finite_singleton _)
  · rintro W' (⟨s, h, rfl⟩ | ⟨r, h, rfl⟩)
    · subst h
      exact fd_resL W
    · subst h
      exact fd_resR W
  have key : ∀ (r s : ℕ) (h : r + s = N), ∃ T : Finset (GL (Fin (r + s)) (Af E)), ∀ g : GA E (r + s),
      ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (t : GL (Fin (r + s)) (Af E)) (k : Kinf E (r + s))
        (l : GL (Fin (r + s)) (Af E)), t ∈ T ∧ l ∈ (h ▸ K : Subgroup (GL (Fin (r + s)) (Af E))) ∧
        g = unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l := by
    intro r s h
    subst h
    exact GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets E r s K hK
  have hopen : ∀ (r s : ℕ) (h : r + s = N),
      IsOpen ((h ▸ K : Subgroup (GL (Fin (r + s)) (Af E))) : Set (GL (Fin (r + s)) (Af E))) := by
    intro r s h
    subst h
    exact hK
  choose T hT using key
  refine ⟨fun M => {K' | ∃ s, ∃ h : M + s = N, K' ∈ (fun t => Slice1.levelOne s (h ▸ K) t ⊓ KO E M) '' (T M s h : Set _)} ∪
    {K' | ∃ r, ∃ h : r + M = N, K' ∈ (fun t => SliceR.levelTwo (h ▸ K) t ⊓ KO E M) '' (T r M h : Set _)},
    fun M => ⟨?_, ?_⟩, ?_⟩
  · exact (finite_sig (hu₁ M) _ fun _ _ => (Finset.finite_toSet _).image _).union
      (finite_sig (hu₂ M) _ fun _ _ => (Finset.finite_toSet _).image _)
  · rintro K' (⟨s, h, t, -, rfl⟩ | ⟨r, h, t, -, rfl⟩)
    · rw [Subgroup.coe_inf]
      exact (Slice1.isOpen_levelOne (hopen M s h) t).inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E M)
    · rw [Subgroup.coe_inf]
      exact (SliceR.isOpen_levelTwo (hopen r M h) t).inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E M)
  · intro r s h V V₁ V₂ z₁ z₂ _ _ _ hty hemb
    have hT' := hT r s h
    subst h
    obtain ⟨t, ht, h₁, h₂⟩ := blocks hT' hty hemb
    exact ⟨⟨_, Or.inl ⟨s, rfl, t, ht, rfl⟩, _, Or.inl ⟨s, rfl, rfl⟩, h₁⟩,
      ⟨_, Or.inr ⟨r, rfl, t, ht, rfl⟩, _, Or.inr ⟨r, rfl, rfl⟩, h₂⟩⟩

end GlobalTheory.CompanionTheory.LimV.BlockTy

end
