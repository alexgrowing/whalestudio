import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocCompSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquiv
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.SplitEigen

theorem exists_eigen_of_mem_iSup {G V U ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U]
    [Module ℂ U] (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible)
    (f : ι → U →ₗ[ℂ] V) (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Set G) (c : G → ℂ) (φ : V) (h0 : φ ≠ 0)
    (hK : ∀ k ∈ K, ρ k φ = c k • φ) (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) :
    ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = c k • v := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  have key : ∀ s : Finset ι, ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → φ ∉ W →
      φ ∈ W ⊔ ⨆ i ∈ s, LinearMap.range (f i) → ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = c k • v := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro W _ h1 h2; exact absurd (by simpa using h2) h1
    | insert i s _ ih =>
      intro W hW h1 h2
      rw [Finset.iSup_insert, ← sup_assoc] at h2
      by_cases h3 : φ ∈ W ⊔ LinearMap.range (f i)
      · obtain ⟨x, hx, _, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 h3
        have hv : f i v ∉ W := fun h => h1 (e ▸ add_mem hx h)
        have hc : W.comap (f i) = ⊥ := by
          refine (((isIrreducible_iff σ).1 hσ).2 _ fun g u hu => ?_).resolve_right fun h => hv ?_
          · rw [Submodule.mem_comap, hf]; exact hW g _ hu
          · have : v ∈ W.comap (f i) := h ▸ Submodule.mem_top
            exact this
        refine ⟨v, fun h => hv (by rw [h, map_zero]; exact zero_mem _), fun k hk => ?_⟩
        have h4 : σ k v - c k • v ∈ W.comap (f i) := by
          have h5 := hK k hk
          rw [← e, map_add] at h5
          have h6 : f i (σ k v - c k • v) = c k • x - ρ k x := by
            rw [map_sub, hf, map_smul]; rw [smul_add] at h5; linear_combination (norm := module) h5
          rw [Submodule.mem_comap, h6]
          exact sub_mem (W.smul_mem _ hx) (hW k x hx)
        rw [hc, Submodule.mem_bot] at h4
        exact sub_eq_zero.1 h4
      · refine ih _ (fun g y hy => ?_) h3 h2
        obtain ⟨x, hx, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add, ← hf]
        exact Submodule.add_mem_sup (hW g x hx) ⟨_, rfl⟩
  exact key s ⊥ (fun g x hx => by simp_all) (by simpa using h0) (by simpa using hs)

theorem exists_locComp_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Submodule ℂ (UA E n → ℂ)), IsAutRepU U → ∀ w, IsSplitAt w → ∀ (J : Subgroup (GL (Fin n) (w.adicCompletion E))), IsOpen (J : Set (GL (Fin n) (w.adicCompletion E))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion E))) → ∀ (χ : J →* ℂˣ) (φ : UA E n → ℂ), φ ∈ U → φ ≠ 0 → (∀ x ∈ locU n w, ∀ hx : cLoc w x ∈ J, RU E n x φ = (χ ⟨_, hx⟩ : ℂ) • φ) → ∃ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ ∃ v : σ.V, v ≠ 0 ∧ ∀ g : J, σ.ρ g v = (χ g : ℂ) • v := by
  classical
  intro E _ _ _ n U hU w hw J _ _ χ φ hφ h0 hχ
  let π : AutSub E n := ⟨U, hU⟩
  obtain ⟨σ, -, hσ, -⟩ := GlobalTheory.DefU.exists_locComp_split E n π w hw
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hw
  obtain ⟨r, -, -, hr2⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have hcl : ∀ g, cLoc w ((e.symm g : locU n w) : UA E n) = g := fun g => by
    rw [← he, e.apply_symm_apply]
  let p : locU n w →* GL (Fin n) (w.adicCompletion E) := (cLoc w).comp (locU n w).subtype
  have hp : p = e.toMulEquiv.toMonoidHom := MonoidHom.ext fun x => (he x).symm
  let σ' : Representation ℂ (locU n w) σ.V := σ.ρ.comp p
  have hirr : σ'.IsIrreducible := by
    change Representation.IsIrreducible (σ.ρ.comp p); rw [hp]; exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv σ.ρ e.toMulEquiv σ.irred
  refine ⟨σ, hσ, ?_⟩
  obtain ⟨-, f, hf0, hfm, hf⟩ := hσ
  let F : σ'.IntertwiningMap (π.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h =>
    hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
  have hsup := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) π.V σ.V σ.V π.rep (locU n w).subtype
    σ' σ' π.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr2 g y⟩) F hF0).1
  let c : locU n w → ℂ := fun k => if h : cLoc w (k : UA E n) ∈ J then (χ ⟨_, h⟩ : ℂ) else 0
  obtain ⟨v, hv0, hv⟩ := exists_eigen_of_mem_iSup (π.rep.comp (locU n w).subtype) σ' hirr
    (fun h : σ'.IntertwiningMap (π.rep.comp (locU n w).subtype) => h.toLinearMap)
    (fun h g u => LinearMap.congr_fun (h.isIntertwining' g) u)
    {k | cLoc w (k : UA E n) ∈ J} c ⟨φ, hφ⟩
    (fun h => h0 (congrArg Subtype.val h))
    (fun k hk => Subtype.ext (by
      change RU E n (k : UA E n) φ = c k • φ
      show RU E n (k : UA E n) φ = (if h : cLoc w (k : UA E n) ∈ J then (χ ⟨_, h⟩ : ℂ) else 0) • φ
      have hk' : cLoc w (k : UA E n) ∈ J := hk
      rw [dif_pos hk']
      exact hχ _ k.2 hk'))
    (hsup ▸ Submodule.mem_top)
  refine ⟨v, hv0, fun g => ?_⟩
  have hk : cLoc w ((e.symm g : locU n w) : UA E n) ∈ J := by rw [hcl]; exact g.2
  have h1 := hv (e.symm g) hk
  have h2 : σ' (e.symm g) = σ.ρ g := by
    change σ.ρ (cLoc w ((e.symm g : locU n w) : UA E n)) = _
    rw [hcl]
  rw [h2] at h1
  rw [h1]
  simp only [c, dif_pos hk]
  congr 3
  exact Subtype.ext (hcl g)

end GlobalTheory.SplitEigen
