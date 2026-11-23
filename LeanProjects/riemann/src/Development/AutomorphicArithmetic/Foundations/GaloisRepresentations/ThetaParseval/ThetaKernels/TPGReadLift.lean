import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ReadLift
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TP
open scoped Classical
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}
private theorem pure_mem_pol_pk {B : Base F E} {M : Model σ X W} {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb)
    {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (h : IsFin M φ) : pure f φ ∈ PolData B M :=
  Submodule.subset_span ⟨f, hf, φ, h.1, h.2, rfl⟩
private theorem pure_add'_pk {κ : Type} [Fintype κ] (f g : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure (f + g) φ = pure f φ + pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
private theorem pure_smul'_pk {κ : Type} [Fintype κ] (a : ℂ) (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure (a • f) φ = a • pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
private theorem isFin_update_pk {M : Model σ X W} {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (h : IsFin M φ) (v : Pl F)
    {ψ : (Fin n × Fin d → Fv F v) → ℂ} (hψ : ψ ∈ SB (Fin n × Fin d → Fv F v)) : IsFin M (Function.update φ v ψ) := by
  refine ⟨fun u => ?_, ?_⟩
  · by_cases hu : u = v
    · subst hu
      simpa using hψ
    · simpa [Function.update_of_ne hu] using h.1 u
  · filter_upwards [h.2, Filter.eventually_cofinite_ne v] with u hu hne
    rw [Function.update_of_ne hne]
    exact hu
end Gen
private theorem irr_pull_pk {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (q : H →* G) (hq : Function.Surjective q) (h : ρ.IsIrreducible) : Representation.IsIrreducible (ρ.comp q : Representation ℂ H V) := by
  rw [GlobalTheory.CuspRep.isIrreducible_iff] at h ⊢
  refine ⟨h.1, fun U hU => h.2 U fun g v hv => ?_⟩
  obtain ⟨x, rfl⟩ := hq g
  exact hU x v hv
section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
private theorem isSplit_prime_pk (hc : IsCMExt (maximalRealSubfield E) E (cj E)) {v : Pl (maximalRealSubfield E)}
    (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v) : GlobalTheory.UnitaryBC.IsSplitAt (splitPrime t) :=
  ⟨splitPrime (t.comp (cj E)), splitPrime_comp_ne hc t, by rw [splitPrime_under, splitPrime_under]⟩
private theorem cLoc_surj_pk (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (hw : GlobalTheory.UnitaryBC.IsSplitAt w) :
    Function.Surjective ((GlobalTheory.UnitaryBC.cLoc (n := a) w).comp (GlobalTheory.UnitaryBC.locU a w).subtype) := fun g => by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  exact ⟨e.symm g, by rw [MonoidHom.comp_apply, Subgroup.coe_subtype, ← he, e.apply_symm_apply]⟩
private theorem decomp_loc_pk (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (hw : GlobalTheory.UnitaryBC.IsSplitAt w) (g : GlobalTheory.UnitaryBC.UA E a) :
    ∃ h ∈ GlobalTheory.UnitaryBC.locU a w, ∀ h' ∈ GlobalTheory.UnitaryBC.locU a w, Commute (h⁻¹ * g) h' := by
  obtain ⟨x, hx, y, rfl, hy⟩ := GlobalTheory.Cong.exists_locU_mul_comm a w hw g
  exact ⟨x, hx, fun z hz => by rw [inv_mul_cancel_left]; exact hy z hz⟩
private theorem read_pair_pk {n d : ℕ} (w : HeightOneSpectrum (𝓞 E)) (hw : GlobalTheory.UnitaryBC.IsSplitAt w) (hA : AbsIso)
    {U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)} {U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ)}
    (hU : GlobalTheory.UnitaryBC.IsAutRepU U) (hU' : GlobalTheory.UnitaryBC.IsAutRepU U')
    (τ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion E))) (τ' : GlobalTheory.CuspRep.SmIrr (GL (Fin d) (w.adicCompletion E)))
    (hτ : CompAt U w τ) (hτ' : CompAt U' w τ')
    (P : (GlobalTheory.UnitaryBC.UA E n → ℂ) →+ (GlobalTheory.UnitaryBC.UA E d → ℂ)) (hPU : ∀ φ ∈ U, P φ ∈ U')
    {φ : GlobalTheory.UnitaryBC.UA E n → ℂ} (hφ : φ ∈ U) (hne : P φ ≠ 0) :
    ∃ (c : τ.V →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ)) (p : (GlobalTheory.UnitaryBC.UA E d → ℂ) →ₗ[ℂ] τ'.V) (x : τ.V),
      (∀ y, c y ∈ U) ∧
      (∀ (h : GlobalTheory.UnitaryBC.locU n w) y, c (τ.ρ (GlobalTheory.UnitaryBC.cLoc w h.1) y) = GlobalTheory.UnitaryBC.RU E n h.1 (c y)) ∧
      (∀ (h : GlobalTheory.UnitaryBC.locU d w), ∀ y ∈ U',
        p (GlobalTheory.UnitaryBC.RU E d h.1 y) = τ'.ρ (GlobalTheory.UnitaryBC.cLoc w h.1) (p y)) ∧
      p (P (c x)) ≠ 0 := by
  obtain ⟨hirr, f, hf0, hfU, hfe⟩ := hτ
  obtain ⟨hirr', f', hf0', hfU', hfe'⟩ := hτ'
  obtain ⟨⟨m, c, x, hcU, hce, hsum⟩, -⟩ := hA (GlobalTheory.UnitaryBC.UA E n) (GlobalTheory.UnitaryBC.UA E n → ℂ) τ.V (GlobalTheory.UnitaryBC.RU E n) U
    (GlobalTheory.UnitaryBC.locU n w) (τ.ρ.comp ((GlobalTheory.UnitaryBC.cLoc w).comp (GlobalTheory.UnitaryBC.locU n w).subtype))
    (decomp_loc_pk n w hw) hU.stable hU.irred (irr_pull_pk _ _ (cLoc_surj_pk n w hw) hirr) f hf0 hfU hfe φ hφ
  obtain ⟨p, hp0, hpe⟩ := (hA (GlobalTheory.UnitaryBC.UA E d) (GlobalTheory.UnitaryBC.UA E d → ℂ) τ'.V (GlobalTheory.UnitaryBC.RU E d) U'
    (GlobalTheory.UnitaryBC.locU d w) (τ'.ρ.comp ((GlobalTheory.UnitaryBC.cLoc w).comp (GlobalTheory.UnitaryBC.locU d w).subtype))
    (decomp_loc_pk d w hw) hU'.stable hU'.irred (irr_pull_pk _ _ (cLoc_surj_pk d w hw) hirr') f' hf0' hfU' hfe' (P φ) (hPU φ hφ)).2 hne
  have hs : ∑ i, p (P (c i (x i))) ≠ 0 := by
    rw [← map_sum, ← map_sum, ← hsum]
    exact hp0
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  exact ⟨c i, p, x i, hcU i, fun h y => hce i h y, fun h y hy => hpe h y hy, hi⟩
end CM
section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ}
  {B : Base (maximalRealSubfield E) E} {X : Spc (maximalRealSubfield E) E n} {W : Spc (maximalRealSubfield E) E d}
  {M : Model (cj E) X W} {χX χW : Chr (maximalRealSubfield E) E} {om : Rep (cj E) X W}
  {e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J} {e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J}
theorem std_of_fin_k (hP : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0) {φ : ∀ v : Pl (maximalRealSubfield E), (Fin n × Fin d → Fv (maximalRealSubfield E) v) → ℂ}
    (h : IsFin M φ) : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers (maximalRealSubfield E)} 1 := by
  filter_upwards [h.2, hP.good.std] with v a b using a.trans b
theorem real_part_k (hP : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0)
    (Θ : PolData B M →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ) →ₛₗ[starRingEnd ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ))
    (hΘ : ∀ (Φ : PolData B M) φ, GlobalTheory.UnitaryBC.IsAutFormU φ → Θ Φ φ = lift M om Φ.1 (φ ∘ e.symm) ∘ e' ∧ GlobalTheory.UnitaryBC.IsAutFormU (Θ Φ φ) ∧
      ∀ g h, ∃ Φ₁ : PolData B M, Φ₁.1 = om (e g, e' h) Φ.1 ∧
        Θ Φ₁ (GlobalTheory.UnitaryBC.RU E n g φ) = GlobalTheory.UnitaryBC.RU E d h (Θ Φ φ))
    {U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ)} {pr : (GlobalTheory.UnitaryBC.UA E d → ℂ) →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ)}
    (hp : ∀ f, GlobalTheory.UnitaryBC.IsAutFormU f → pr f ∈ U' ∧ ∀ x, pr (GlobalTheory.UnitaryBC.RU E d x f) = GlobalTheory.UnitaryBC.RU E d x (pr f))
    {f₀ : SInf (maximalRealSubfield E) (Fin n × Fin d)} (hf₀ : f₀ ∈ M.Pol B.ψ B.emb) {φ : GlobalTheory.UnitaryBC.UA E n → ℂ}
    (hφ : GlobalTheory.UnitaryBC.IsAutFormU φ) {φf : ∀ v : Pl (maximalRealSubfield E), (Fin n × Fin d → Fv (maximalRealSubfield E) v) → ℂ}
    (hfin : IsFin M φf) (hne : pr (Θ ⟨pure f₀ φf, pure_mem_pol_pk hf₀ hfin⟩ φ) ≠ 0)
    {w : InfinitePlace (maximalRealSubfield E)} {lam' : DomWeight d} (hT : HasType B M om e' f₀ w lam') :
    GlobalTheory.UnitaryBC.HasWeightAt U' (B.emb w).1 lam' := by
  obtain ⟨hirr, i, hi, ⟨x₀, hx₀⟩, hact⟩ := hT
  let Ψ : nablaSq ℂ d lam' → PolData B M := fun x => ⟨pure (i x) φf, pure_mem_pol_pk (hi x) hfin⟩
  have hadd : ∀ x y, Ψ (x + y) = Ψ x + Ψ y := fun x y => Subtype.ext (by
    change pure (i (x + y)) φf = pure (i x) φf + pure (i y) φf
    rw [map_add, pure_add'_pk])
  have hsm : ∀ (a : ℂ) x, Ψ (a • x) = a • Ψ x := fun a x => Subtype.ext (by
    change pure (i (a • x)) φf = a • pure (i x) φf
    rw [map_smul, pure_smul'_pk])
  refine ⟨hirr, { toFun := fun x => pr (Θ (Ψ x) φ), map_add' := fun x y => ?_, map_smul' := fun a x => ?_ }, ?_,
    fun x => (hp _ (hΘ _ _ hφ).2.1).1, fun k x => ?_⟩
  · simp only [hadd, map_add, LinearMap.add_apply]
  · simp only [hsm, map_smul, LinearMap.smul_apply, RingHom.id_apply]
  · intro h0
    apply hne
    have h1 := LinearMap.congr_fun h0 x₀
    have h2 : Ψ x₀ = ⟨pure f₀ φf, pure_mem_pol_pk hf₀ hfin⟩ := Subtype.ext (by
      change pure (i x₀) φf = pure f₀ φf
      rw [hx₀])
    simpa [h2] using h1
  · obtain ⟨Φ₁, h1, h2⟩ := (hΘ (Ψ x) φ hφ).2.2 1 k.1
    have e1 : Φ₁ = Ψ (GlobalTheory.Branching.sqRep ℂ d lam' (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k.1) x) := Subtype.ext (by
      rw [h1, map_one]
      exact PositivityTheory.ThKG.Loc.Cone.pure_real (hact k.1 k.2 x) φf hfin.1 (_root_.UpperTheory.TP.std_of_fin_k hP hfin))
    rw [map_one, Module.End.one_apply, e1] at h2
    change pr (Θ (Ψ _) φ) = GlobalTheory.UnitaryBC.RU E d k.1 (pr (Θ (Ψ x) φ))
    rw [← (hp _ (hΘ (Ψ x) φ hφ).2.1).2 k.1, ← h2]
    rfl
end Main
section Split
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ}
  {B : Base (maximalRealSubfield E) E} {X : Spc (maximalRealSubfield E) E n} {W : Spc (maximalRealSubfield E) E d}
  {M : Model (cj E) X W} {χX χW : Chr (maximalRealSubfield E) E} {om : Rep (cj E) X W}
  {e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J} {e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J}
private theorem read_point_pk {a : ℕ} {Y : Spc (maximalRealSubfield E) E a} {ε : GlobalTheory.UnitaryBC.UA E a ≃ₜ* UA (cj E) Y.J} (hε : IsBr Y ε)
    (hc : IsCMExt (maximalRealSubfield E) E (cj E)) {v : Pl (maximalRealSubfield E)}
    (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v) (g : GL (Fin a) (Fv (maximalRealSubfield E) v)) :
    ∃ x : GlobalTheory.UnitaryBC.locU a (splitPrime t), ε x.1 ∈ UAt (cj E) Y (evFin (maximalRealSubfield E) v) ∧
      g.1 = (mat (ε x.1)).map (piW t) ∧
      GlobalTheory.UnitaryBC.cLoc (splitPrime t) x.1 = Matrix.GeneralLinearGroup.map (complMap (splitPrime_under t)) g := by
  obtain ⟨x, hx⟩ := cLoc_surj_pk a (splitPrime t) (isSplit_prime_pk hc t) (Matrix.GeneralLinearGroup.map (complMap (splitPrime_under t)) g)
  have hx' : GlobalTheory.UnitaryBC.cLoc (splitPrime t) x.1 = Matrix.GeneralLinearGroup.map (complMap (splitPrime_under t)) g := hx
  refine ⟨x, ?_, ?_, hx'⟩
  · have h1 := (hε.loc (splitPrime t) x.1).2 x.2
    rw [splitPrime_under] at h1
    exact GlobalTheory.ThK.Dbl.Inert.mem_locGrp h1
  · have h1 := hε.spl v t x.1
    rw [hx'] at h1
    have hinj : Function.Injective (complMap (splitPrime_under t)) := (complMap (splitPrime_under t)).injective
    exact Matrix.map_injective hinj h1.symm
end Split
section Split2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ}
  {B : Base (maximalRealSubfield E) E} {X : Spc (maximalRealSubfield E) E n} {W : Spc (maximalRealSubfield E) E d}
  {M : Model (cj E) X W} {χX χW : Chr (maximalRealSubfield E) E} {om : Rep (cj E) X W}
  {e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J} {e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J}
theorem split_part_k (T : _root_.UpperTheory.TP.Tools_k) (hA : AbsIso) (hP : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0) (he : IsBr X e) (he' : IsBr W e')
    (Θ : PolData B M →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ) →ₛₗ[starRingEnd ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ))
    (hΘ : ∀ (Φ : PolData B M) φ, GlobalTheory.UnitaryBC.IsAutFormU φ → Θ Φ φ = lift M om Φ.1 (φ ∘ e.symm) ∘ e' ∧ GlobalTheory.UnitaryBC.IsAutFormU (Θ Φ φ) ∧
      ∀ g h, ∃ Φ₁ : PolData B M, Φ₁.1 = om (e g, e' h) Φ.1 ∧
        Θ Φ₁ (GlobalTheory.UnitaryBC.RU E n g φ) = GlobalTheory.UnitaryBC.RU E d h (Θ Φ φ))
    {U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)} {U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ)}
    {pr : (GlobalTheory.UnitaryBC.UA E d → ℂ) →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ)}
    (hU : GlobalTheory.UnitaryBC.IsAutRepU U) (hU' : GlobalTheory.UnitaryBC.IsAutRepU U')
    (hp : ∀ f, GlobalTheory.UnitaryBC.IsAutFormU f → pr f ∈ U' ∧ ∀ x, pr (GlobalTheory.UnitaryBC.RU E d x f) = GlobalTheory.UnitaryBC.RU E d x (pr f))
    {f₀ : SInf (maximalRealSubfield E) (Fin n × Fin d)} (hf₀ : f₀ ∈ M.Pol B.ψ B.emb) {φ : GlobalTheory.UnitaryBC.UA E n → ℂ}
    (hφ : φ ∈ U) {φf : ∀ v : Pl (maximalRealSubfield E), (Fin n × Fin d → Fv (maximalRealSubfield E) v) → ℂ}
    (hfin : IsFin M φf) (hne : pr (Θ ⟨pure f₀ φf, pure_mem_pol_pk hf₀ hfin⟩ φ) ≠ 0)
    {v : Pl (maximalRealSubfield E)} (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v)
    (τ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) ((splitPrime t).adicCompletion E)))
    (τ' : GlobalTheory.CuspRep.SmIrr (GL (Fin d) ((splitPrime t).adicCompletion E)))
    (hτ : CompAt U (splitPrime t) τ) (hτ' : CompAt U' (splitPrime t) τ') : LocPair t χX χW τ τ' := by
  have hc := hP.base.cm
  have hw := isSplit_prime_pk hc t
  let Φ₀ : PolData B M := ⟨pure f₀ φf, pure_mem_pol_pk hf₀ hfin⟩
  let P : (GlobalTheory.UnitaryBC.UA E n → ℂ) →+ (GlobalTheory.UnitaryBC.UA E d → ℂ) :=
    { toFun := fun y => pr (Θ Φ₀ y), map_zero' := by simp, map_add' := fun a b => by simp }
  obtain ⟨c, p, x₀, hcU, hce, hpe, hp0⟩ := read_pair_pk (splitPrime t) hw hA hU hU' τ τ' hτ hτ' P
    (fun y hy => (hp _ (hΘ _ _ (hU.aut y hy)).2.1).1) hφ hne
  obtain ⟨⟨ι, hι⟩, hSM⟩ := T.split _ E (cj E) B n d X W M χX χW om n 0 d 0 hP v t
  have hSM := hSM ι hι
  have hbij : Set.BijOn ι (SB (Fin n × Fin d → Fv (maximalRealSubfield E) v) : Set _)
      (SB (Matrix (Fin n) (Fin d) (Fv (maximalRealSubfield E) v)) : Set _) := Model.IsLin.bij hι
  let ιe : SB (Fin n × Fin d → Fv (maximalRealSubfield E) v) ≃ₗ[ℂ] SB (Matrix (Fin n) (Fin d) (Fv (maximalRealSubfield E) v)) :=
    LinearEquiv.ofBijective (ι.restrict fun y hy => hbij.mapsTo hy)
      ⟨fun a b h => Subtype.ext (hbij.injOn a.2 b.2 (congrArg Subtype.val h)), fun b => by
        obtain ⟨a, ha, hab⟩ := hbij.surjOn b.2
        exact ⟨⟨a, ha⟩, Subtype.ext hab⟩⟩
  have hfu : ∀ ψ : SB (Fin n × Fin d → Fv (maximalRealSubfield E) v), IsFin M (Function.update φf v ψ.1) :=
    fun ψ => isFin_update_pk hfin v ψ.2
  let Ψ : SB (Fin n × Fin d → Fv (maximalRealSubfield E) v) → PolData B M :=
    fun ψ => ⟨pure f₀ (Function.update φf v ψ.1), pure_mem_pol_pk hf₀ (hfu ψ)⟩
  have hPA := PositivityTheory.ThKF.pureAct (maximalRealSubfield E) (Fin n × Fin d) v id f₀ φf hfin.1 (_root_.UpperTheory.TP.std_of_fin_k hP hfin)
  have hz : pure f₀ (Function.update φf v 0) = 0 :=
    PositivityTheory.ThKG.Loc.Cone.pure_zero f₀ _ (GlobalTheory.PureFactor.update_eventually φf v 0 (_root_.UpperTheory.TP.std_of_fin_k hP hfin)) v (by simp)
  have hadd : ∀ a b, Ψ (a + b) = Ψ a + Ψ b := fun a b => Subtype.ext (by
    have := hPA.2.1 a.1 b.1 1
    rw [one_smul, one_smul] at this
    exact this)
  have hsm : ∀ (r : ℂ) a, Ψ (r • a) = r • Ψ a := fun r a => Subtype.ext (by
    have := hPA.2.1 0 a.1 r
    rw [zero_add, hz, zero_add] at this
    exact this)
  let A : SB (Fin n × Fin d → Fv (maximalRealSubfield E) v) →ₗ[ℂ] τ.V →ₛₗ[starRingEnd ℂ] τ'.V :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun ψ x => p (pr (Θ (Ψ ψ) (c x))))
      (fun a b x => by simp only [hadd, map_add, LinearMap.add_apply])
      (fun r a x => by simp only [hsm, map_smul, LinearMap.smul_apply, RingHom.id_apply])
      (fun a x y => by simp only [map_add])
      (fun r a x => by simp only [map_smul, map_smulₛₗ])
  refine ⟨A ∘ₗ ιe.symm.toLinearMap, ?_, fun g h Φ Φ₁ hΦ x => ?_⟩
  · intro h0
    apply hp0
    have h1 := LinearMap.congr_fun (LinearMap.congr_fun h0 (ιe ⟨φf v, hfin.1 v⟩)) x₀
    have h2 : Ψ ⟨φf v, hfin.1 v⟩ = Φ₀ := Subtype.ext (by
      change pure f₀ (Function.update φf v (φf v)) = pure f₀ φf
      rw [Function.update_eq_self])
    simpa [A, h2, P] using h1
  · obtain ⟨ĝ, hg1, hg2, hg3⟩ := read_point_pk he hc t g
    obtain ⟨ĥ, hh1, hh2, hh3⟩ := read_point_pk he' hc t h
    set ψ := ιe.symm Φ with hψ
    have hιψ : ι ψ.1 = Φ.1 := by
      have := congrArg Subtype.val (ιe.apply_symm_apply Φ)
      exact this
    obtain ⟨ψ₁, ⟨hψ₁, hact⟩, -⟩ := (T.acts _ E (cj E) B n d X W M χX χW om n 0 d 0 hP v).1 _ hg1 _ hh1 ψ.1 ψ.2
    have hι₁ : ι ψ₁ = Φ₁.1 := by
      rw [hΦ, ← hιψ]
      exact hSM _ hg1 _ hh1 g h hg2 hh2 _ ψ.2 _ hψ₁ hact
    have hψ₁' : ιe.symm Φ₁ = ⟨ψ₁, hψ₁⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext hι₁.symm
    have hΦ₁ := hΘ (Ψ ψ) (c x) (hU.aut _ (hcU x))
    obtain ⟨Φ₂, h1, h2⟩ := hΦ₁.2.2 ĝ.1 ĥ.1
    have hΦ₂ : Φ₂ = Ψ ⟨ψ₁, hψ₁⟩ := Subtype.ext (by
      rw [h1]
      have := (PositivityTheory.ThKF.pureAct (maximalRealSubfield E) (Fin n × Fin d) v (om (e ĝ.1, e' ĥ.1)) f₀ (Function.update φf v ψ.1) (hfu ψ).1
        (_root_.UpperTheory.TP.std_of_fin_k hP (hfu ψ))).2.2 ψ₁ (by simpa using hact)
      refine this.trans ?_
      change pure f₀ (Function.update (Function.update φf v ψ.1) v ψ₁) = pure f₀ (Function.update φf v ψ₁)
      rw [Function.update_idem])
    change p (pr (Θ (Ψ (ιe.symm Φ₁)) (c (τ.ρ _ x)))) = τ'.ρ _ (p (pr (Θ (Ψ ψ) (c x))))
    rw [hψ₁', ← hΦ₂, ← hg3, ← hh3, hce ĝ x, h2, (hp _ hΦ₁.2.1).2, hpe ĥ _ (hp _ hΦ₁.2.1).1]
end Split2
theorem readLift_k : _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.LiftAut_k → AbsIso → _root_.UpperTheory.TP.ReadLift_k := by
  intro T hL hA E _ _ _ B n d X W M χX χW om hP hn e e' he he' U U' pr hU hU' hp f₀ hf₀ φ hφ φf hfin hne
  obtain ⟨Θ, hΘ⟩ := hL E B n d X W M χX χW om hP hn e e' he he'
  have hne' : pr (Θ ⟨pure f₀ φf, pure_mem_pol_pk hf₀ hfin⟩ φ) ≠ 0 := by
    rw [(hΘ ⟨_, pure_mem_pol_pk hf₀ hfin⟩ φ (hU.aut φ hφ)).1]
    exact hne
  exact ⟨fun w lam' hT => _root_.UpperTheory.TP.real_part_k hP Θ hΘ hp hf₀ (hU.aut φ hφ) hfin hne' hT,
    fun v t τ τ' hτ hτ' => _root_.UpperTheory.TP.split_part_k T hA hP he he' Θ hΘ hU hU' hp hf₀ hφ hfin hne' t τ τ' hτ hτ'⟩
end UpperTheory.TP
end
end
