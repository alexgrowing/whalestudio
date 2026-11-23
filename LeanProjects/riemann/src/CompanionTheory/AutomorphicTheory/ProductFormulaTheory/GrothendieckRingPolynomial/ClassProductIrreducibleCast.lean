import Mathlib
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GelfandKazhdanContragredientImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LocalLanglandsOfIrreducibleAdmissibleImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ProductTransposeInverseDualReverseImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ContragredientProductIrreducibleImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DualClassInvolutiveImports
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGLStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth.GrothendieckCommutativity

section Pull

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def subComp {π : Representation ℂ G V} (s : H →* G) (S : Subrepresentation π) : Subrepresentation (π.comp s) :=
  ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (s g) hv⟩

def subQuotComp {π : Representation ℂ G V} (s : H →* G) (S T : Subrepresentation π) :
    Representation.Equiv (subQuot (subComp s S) (subComp s T)) ((subQuot S T).comp s) :=
  .mk (LinearEquiv.refl ℂ _) fun _ => rfl

def equivComp {σ : Representation ℂ G V} {τ : Representation ℂ G W} (φ : σ.Equiv τ) (s : H →* G) :
    Representation.Equiv (σ.comp s) (τ.comp s) :=
  .mk φ.toLinearEquiv fun g => φ.isIntertwining' (s g)

theorem occursTimes_comp {σ : Representation ℂ G W} {π : Representation ℂ G V} (s : H →* G) {r : ℕ}
    (h : OccursTimes σ π r) : OccursTimes (σ.comp s) (π.comp s) r := by
  obtain ⟨S, T, h1, h2, h3⟩ := h
  exact ⟨fun i => subComp s (S i), fun i => subComp s (T i), fun i => h1 i, fun i j hij => h2 i j hij,
    fun i => (h3 i).map fun φ => (subQuotComp s (S i) (T i)).trans (equivComp φ s)⟩

theorem jhMult_le_comp (σ : Representation ℂ G W) (π : Representation ℂ G V) (s : H →* G) :
    jhMult σ π ≤ jhMult (σ.comp s) (π.comp s) :=
  iSup₂_le fun r h => le_iSup₂_of_le (f := fun r (_ : OccursTimes (σ.comp s) (π.comp s) r) => (r : ℕ∞)) r
    (occursTimes_comp s h) le_rfl

end Pull

section Contra

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {π : Representation ℂ G V}

def ann (T : Subrepresentation π) : Subrepresentation (contra π) where
  toSubmodule :=
    { carrier := {l | ∀ v ∈ T.toSubmodule, (l : Module.Dual ℂ V) v = 0}
      add_mem' := fun {a b} ha hb v hv => by
        rw [Submodule.coe_add, LinearMap.add_apply, ha v hv, hb v hv, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun c l hl v hv => by
        rw [Submodule.coe_smul, LinearMap.smul_apply, hl v hv, smul_zero] }
  apply_mem_toSubmodule g l hl v hv := by
    show (l : Module.Dual ℂ V) (π g⁻¹ v) = 0
    exact hl _ (T.apply_mem_toSubmodule g⁻¹ hv)

theorem ann_anti {S T : Subrepresentation π} (h : T ≤ S) : ann S ≤ ann T :=
  fun _ hl v hv => hl v (h hv)

variable (S T : Subrepresentation π)

def formOf (l : (ann T).toSubmodule) : Module.Dual ℂ (S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :=
  (T.toSubmodule.comap S.toSubmodule.subtype).liftQ ((l.1 : Module.Dual ℂ V) ∘ₗ S.toSubmodule.subtype)
    fun w hw => LinearMap.mem_ker.2 (l.2 _ hw)

theorem formOf_mem (l : (ann T).toSubmodule) : formOf S T l ∈ smoothPart (subQuot S T).dual :=
  mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds l.1.2 (by
      show π.dual 1 (l.1 : Module.Dual ℂ V) = l.1
      rw [map_one]
      rfl)) fun g hg => by
    have hg' : π.dual g (l.1 : Module.Dual ℂ V) = l.1 := hg
    refine LinearMap.ext fun x => ?_
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact LinearMap.congr_fun hg' (w : V))

def annMap : (ann T).toRepresentation.IntertwiningMap (contra (subQuot S T)) where
  toLinearMap :=
    { toFun := fun l => ⟨formOf S T l, formOf_mem S T l⟩
      map_add' := fun a b => Subtype.ext (LinearMap.ext fun x => by
        obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rfl)
      map_smul' := fun c a => Subtype.ext (LinearMap.ext fun x => by
        obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rfl) }
  isIntertwining' g := LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun x => by
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl)

theorem ker_annMap :
    LinearMap.ker (annMap S T).toLinearMap = (ann S).toSubmodule.comap (ann T).toSubmodule.subtype := by
  ext l
  constructor
  · intro hl v hv
    have h0 : annMap S T l = 0 := hl
    exact LinearMap.congr_fun (congrArg Subtype.val h0) (Submodule.Quotient.mk ⟨v, hv⟩)
  · intro hl
    show annMap S T l = 0
    refine Subtype.ext (LinearMap.ext fun x => ?_)
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact hl w.1 w.2

variable {S T}

theorem annMap_surjective
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hπ : IsSmooth π) (hTS : T ≤ S) : Function.Surjective (annMap S T) := by
  intro f
  let m₀ : Module.Dual ℂ S.toSubmodule :=
    (f : Module.Dual ℂ _) ∘ₗ (T.toSubmodule.comap S.toSubmodule.subtype).mkQ
  have hSs : IsSmooth S.toRepresentation := fun w => by
    have : {g : G | S.toRepresentation g w = w} = {g : G | π g w.1 = w.1} := by
      ext g
      exact Subtype.ext_iff
    rw [this]
    exact hπ w.1
  obtain ⟨K, ho, hc, hKs⟩ := hG _ ((isSmooth_contra (subQuot S T) f).mem_nhds (by simp))
  have hm : ∀ h ∈ K, ∀ w, m₀ (S.toRepresentation h w) = m₀ w := by
    intro h hh w
    have h1 : contra (subQuot S T) h⁻¹ f = f := hKs (inv_mem hh)
    have h2 := LinearMap.congr_fun (congrArg Subtype.val h1) (Submodule.Quotient.mk w)
    rw [contra_apply, inv_inv] at h2
    exact h2
  let j : fixed S.toRepresentation K →ₗ[ℂ] fixed π K :=
    { toFun := fun w => ⟨w.1.1, GlobalTheory.ContraRefl.mem_fix.2 fun h hh =>
        congrArg Subtype.val (GlobalTheory.ContraRefl.mem_fix.1 w.2 h hh)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hj : LinearMap.ker j = ⊥ :=
    LinearMap.ker_eq_bot'.2 fun w hw => by
      have h0 := congrArg Subtype.val hw
      exact Subtype.ext (Subtype.ext h0)
  obtain ⟨j', hj'⟩ := LinearMap.exists_leftInverse_of_injective j hj
  let m : Module.Dual ℂ (fixed π K) := (m₀ ∘ₗ (fixed S.toRepresentation K).subtype) ∘ₗ j'
  obtain ⟨l, hlK, hl⟩ := GlobalTheory.ContraRefl.exists_fixed_contra hπ ho hc m
  have hlS : (l : Module.Dual ℂ V) ∘ₗ S.toSubmodule.subtype = m₀ := by
    refine GlobalTheory.ContraRefl.form_ext hSs hc (fun h hh w => ?_) hm (fun w hw => ?_)
    · have h1 := LinearMap.congr_fun (congrArg Subtype.val (hlK h⁻¹ (inv_mem hh))) (w : V)
      rw [contra_apply, inv_inv] at h1
      exact h1
    · have e1 := hl (j ⟨w, hw⟩)
      have e2 := LinearMap.congr_fun hj' ⟨w, hw⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at e2
      show (l : Module.Dual ℂ V) (w : V) = m₀ w
      rw [show (w : V) = ((j ⟨w, hw⟩ : fixed π K) : V) from rfl, e1]
      show m₀ ((fixed S.toRepresentation K).subtype (j' (j ⟨w, hw⟩))) = m₀ w
      rw [e2]
      rfl
  have hlT : l ∈ (ann T).toSubmodule := fun v hv => by
    have h1 := LinearMap.congr_fun hlS ⟨v, hTS hv⟩
    have h2 : (Submodule.Quotient.mk ⟨v, hTS hv⟩ :
        S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hv
    refine h1.trans ?_
    show f.1 ((Submodule.Quotient.mk ⟨v, hTS hv⟩ : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype)) = 0
    rw [h2, map_zero]
  refine ⟨⟨l, hlT⟩, Subtype.ext (LinearMap.ext fun x => ?_)⟩
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact LinearMap.congr_fun hlS w

def annEquiv
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hπ : IsSmooth π) (hTS : T ≤ S) :
    (subQuot (ann T) (ann S)).Equiv (contra (subQuot S T)) :=
  .mk ((Submodule.quotEquivOfEq _ _ (ker_annMap S T).symm).trans
      ((annMap S T).toLinearMap.quotKerEquivOfSurjective (annMap_surjective hG hπ hTS))) fun g => by
    refine LinearMap.ext fun x => ?_
    obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact LinearMap.congr_fun ((annMap S T).isIntertwining' g) l

theorem occursTimes_contra
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hπ : IsSmooth π) {σ : Representation ℂ G W} {r : ℕ} (h : OccursTimes σ π r) :
    OccursTimes (contra σ) (contra π) r := by
  obtain ⟨S, T, h1, h2, h3⟩ := h
  exact ⟨fun i => ann (T (Fin.rev i)), fun i => ann (S (Fin.rev i)), fun i => ann_anti (h1 _),
    fun i j hij => ann_anti (h2 _ _ (Fin.rev_lt_rev.2 hij)),
    fun i => (h3 (Fin.rev i)).map fun φ =>
      (annEquiv hG hπ (h1 (Fin.rev i))).trans (GlobalTheory.ContraRefl.contraEquiv φ.symm)⟩

theorem jhMult_le_contra
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hπ : IsSmooth π) (σ : Representation ℂ G W) : jhMult σ π ≤ jhMult (contra σ) (contra π) :=
  iSup₂_le fun r h => le_iSup₂_of_le (f := fun r (_ : OccursTimes (contra σ) (contra π) r) => (r : ℕ∞)) r
    (occursTimes_contra hG hπ h) le_rfl

end Contra

section Pairs

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prodIrr_congr {h N : ℕ} {z z' : Fin h → IrrGL k} (e : z = z') (hd : ∑ a, (z a).1 = N)
    (hd' : ∑ a, (z' a).1 = N) : Nonempty ((prodIrr z hd).Equiv (prodIrr z' hd')) := by
  subst e
  exact ⟨.refl _⟩

theorem class_product_irreducible_cast {h N M : ℕ} (e : N = M) (z : Fin h → IrrGL k) (hd : ∑ a, (z a).1 = N)
    (hd' : ∑ a, (z a).1 = M) : cl0 (prodIrr z hd) = cl0 (prodIrr z hd') := by
  subst e
  rfl

theorem hasFiniteLength_prodIrr_cast {h N M : ℕ} (e : N = M) (z : Fin h → IrrGL k) (hd : ∑ a, (z a).1 = N)
    (hd' : ∑ a, (z a).1 = M) (hf : HasFiniteLength (prodIrr z hd)) : HasFiniteLength (prodIrr z hd') := by
  subst e
  exact hf

theorem class_congr_equiv {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W} (φ : π.Equiv τ) :
    cl0 π = cl0 τ := by
  by_cases hπ : HasFiniteLength π
  · have hτ := hπ.of_equiv φ
    simp only [cl0, dif_pos hπ, dif_pos hτ]
    exact clsGL_congr φ hπ hτ
  · have hτ : ¬ HasFiniteLength τ := fun h => hπ (h.of_equiv φ.symm)
    simp only [cl0, dif_neg hπ, dif_neg hτ]

theorem class_eq_of_jordan_holder_mult {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W} (hπ : HasFiniteLength π)
    (hτ : HasFiniteLength τ) (h : ∀ σ : IrrRep (GL (Fin N) k), jhMult σ.ρ π = jhMult σ.ρ τ) : cl0 π = cl0 τ := by
  simp only [cl0, dif_pos hπ, dif_pos hτ, clsGL]
  congr 1
  ext c
  rw [cls_apply, cls_apply, h c.rep]

set_option maxHeartbeats 1000000 in

theorem jhMult_pair_le (x y : IrrGL k) {N : ℕ} (h1 : ∑ a, (![x, y] a).1 = N) (h2 : ∑ a, (![y, x] a).1 = N)
    (σ : IrrRep (GL (Fin N) k)) : jhMult σ.ρ (prodIrr ![x, y] h1) ≤ jhMult σ.ρ (prodIrr ![y, x] h2) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hGK : GKLocal k := GlobalTheory.T.local_langlands_of_irreducible_admissible hA
  obtain ⟨hd', ⟨E1⟩⟩ := GlobalTheory.T.product_transpose_inverse_dual_reverse hA hGK ![x, y] h1
  obtain ⟨hd'', ⟨E2⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA (fun a => dualCl (![x, y] (Fin.rev a))) hd'
  have hz : (fun a => dualCl (dualCl (![x, y] (Fin.rev a)))) = ![y, x] := by
    funext a
    fin_cases a
    · exact GlobalTheory.T.dual_class_involutive hA y
    · exact GlobalTheory.T.dual_class_involutive hA x
  obtain ⟨E3⟩ := prodIrr_congr hz hd'' h2
  obtain ⟨G1⟩ := GlobalTheory.T.gelfand_kazhdan_contragredient hGK N σ.ρ σ.smooth σ.irr
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k N
  have hσa : IsAdmissible σ.ρ := hA k N _ σ.ρ σ.smooth σ.irr
  calc jhMult σ.ρ (prodIrr ![x, y] h1)
      ≤ jhMult (σ.ρ.comp (thetaW k N)) ((prodIrr ![x, y] h1).comp (thetaW k N)) := jhMult_le_comp _ _ _
    _ = jhMult (contra σ.ρ) (prodIrr (fun a => dualCl (![x, y] (Fin.rev a))) hd') := by
        rw [jhMult_congr_left G1, jhMult_congr_right _ E1]
    _ ≤ jhMult (contra (contra σ.ρ)) (contra (prodIrr (fun a => dualCl (![x, y] (Fin.rev a))) hd')) :=
        jhMult_le_contra hG (isSmooth_prodIrr _ _) _
    _ = jhMult σ.ρ (prodIrr ![y, x] h2) := by
        rw [← jhMult_congr_left (GlobalTheory.ContraRefl.evEquiv hG hσa), jhMult_congr_right _ E2,
          jhMult_congr_right _ E3]

end Pairs

end CompanionTheory.Groth.GrothendieckCommutativity

namespace CompanionTheory.Groth

open CompanionTheory.Groth.GrothendieckCommutativity

set_option maxHeartbeats 1000000 in

theorem comm (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Comm k := by
  intro x y
  have hxy : ∑ a, (![x, y] a).1 = x.1 + y.1 := by simp [Fin.sum_univ_two]
  have hyx' : ∑ a, (![y, x] a).1 = x.1 + y.1 := by simp [Fin.sum_univ_two, add_comm]
  have hyx : ∑ a, (![y, x] a).1 = y.1 + x.1 := by simp [Fin.sum_univ_two]
  obtain ⟨E1⟩ := nonempty_prod₂_equiv_prodIrr_pair x y hxy
  obtain ⟨E2⟩ := nonempty_prod₂_equiv_prodIrr_pair y x hyx
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have f1 : HasFiniteLength (prod₂ x.rep y.rep) := GlobalTheory.T.parabolicProduct_hasFiniteLength_GL hBZ k _ _ _ _ _ _
    x.2.rep.hasFiniteLength y.2.rep.hasFiniteLength x.2.rep.smooth y.2.rep.smooth
  have f2 : HasFiniteLength (prod₂ y.rep x.rep) := GlobalTheory.T.parabolicProduct_hasFiniteLength_GL hBZ k _ _ _ _ _ _
    y.2.rep.hasFiniteLength x.2.rep.hasFiniteLength y.2.rep.smooth x.2.rep.smooth
  rw [class_congr_equiv E1, class_congr_equiv E2, ← class_product_irreducible_cast (add_comm x.1 y.1) ![y, x] hyx' hyx]
  exact class_eq_of_jordan_holder_mult (f1.of_equiv E1)
    (hasFiniteLength_prodIrr_cast (add_comm y.1 x.1) ![y, x] hyx hyx' (f2.of_equiv E2))
    fun σ => le_antisymm (jhMult_pair_le x y hxy hyx' σ) (jhMult_pair_le y x hyx' hxy σ)

end CompanionTheory.Groth

end
