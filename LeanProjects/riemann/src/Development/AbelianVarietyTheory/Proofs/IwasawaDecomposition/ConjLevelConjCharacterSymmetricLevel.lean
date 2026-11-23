import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemUnipSymBc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameReducesToBasisModPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixModPlaceBasisChangeEqConjStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeeperLevelIffMatricesModPlaceSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarCharacterEqProdAdditiveCharactersRootStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.SymFrame.conj_symLevel : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) → (∀ kv, R.C.P.Div kv.1 (plg kv).1) → (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) → ∀ (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi R.Pg ψ0 → ∀ π : Equiv.Perm (Fin D.R.r), IsSymOrd D.R.rS D.R.k π → ∀ (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), IsRedHom X red → FixRed X red b → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ c : G0g D.nd, ∀ k ∈ X.B.I.Kset, (k ∈ X.K2 ↔ reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H) ∧ ∀ hk : reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H, (((PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨_, hk⟩ : ℂˣ) : ℂ) = star (X.chi2 k) := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R X h eR plg iso hpin hIs hplg hDiv heG ψ0 hψ0 π hπ red b hred hfix hw
  classical
  obtain ⟨P, hP⟩ := GlobalTheory.T.symmetricFrame_reduces_to_basis_mod_place D X h hpin b (fun kv => (hfix kv).1) hw π
  obtain ⟨ψ', a, hψ'1, hchi⟩ := GlobalTheory.T.star_character_eq_prod_additive_characters_root_alt D X h hpin hw
  have hsc : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ d : Fin D.R.r → (ZMod (D.host.g kv.1))ˣ,
      ∀ u : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), u ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k →
        ψ' kv (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a kv i j : ZMod (D.host.g kv.1)) * u.val i j else 0) =
          (ψ0 (plg kv)).compAddMonoidHom (iso kv).toAddMonoidHom
            (edgeSum (symEdge D.R.rS D.R.k) ((GlobalTheory.SeeConjRead.diagGL d)⁻¹ * u * GlobalTheory.SeeConjRead.diagGL d)) := by
    intro kv
    haveI := Fact.mk (D.host.g_prime kv.1)
    refine GlobalTheory.SeeConjScale.scale_conj (Field.toIsField _) D.R.rS D.R.k (ψ' kv) _ (hψ'1 kv) ?_ (a kv)
    intro h1
    apply hψ0 _ (plg kv).2
    ext y
    have := DFunLike.congr_fun h1 ((iso kv).symm y)
    simpa using this
  choose d hd using hsc
  let c : G0g D.nd := fun kv => P kv * GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j))
  refine ⟨c, fun k hk => ?_⟩
  let Ns : G0g D.nd := fun kv => Units.map (Matrix.reindexAlgEquiv (ZMod (D.host.g kv.1)) (ZMod (D.host.g kv.1)) π.symm).toMonoidHom
    ((P kv)⁻¹ * red k kv * P kv)
  have hNs : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) = (((((P kv)⁻¹ * red k kv * P kv) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).submatrix π π := by
    intro kv
    ext i j
    simp [Ns, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  have hMat : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2)
      (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) := by
    intro kv
    rw [hNs kv]
    exact GlobalTheory.Mem.SymFrame.isMatIn_perm _ k _ π (GlobalTheory.T.matrixModPlace_basisChange_eq_conj D X red b hfix kv (hw kv) (P kv) _ (hP kv) k hk)
  have hval : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), reord π (R.eG (eR.symm (c⁻¹ * red k * c))) (plg kv) =
      Formalism.UG.bc ((iso kv : ZMod (D.host.g kv.1) ≃+* kP (plg kv).1) : ZMod (D.host.g kv.1) →+* kP (plg kv).1)
        ((GlobalTheory.SeeConjRead.diagGL (d kv))⁻¹ * Ns kv * GlobalTheory.SeeConjRead.diagGL (d kv)) := by
    intro kv
    have e1 : (c⁻¹ * red k * c) kv = (GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)))⁻¹ *
        ((P kv)⁻¹ * red k kv * P kv) * GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)) := by
      simp only [c, Pi.mul_apply, Pi.inv_apply, mul_inv_rev, mul_assoc]
    have e2 := heG (eR.symm (c⁻¹ * red k * c)) kv
    rw [MulEquiv.apply_symm_apply, e1] at e2
    apply Units.ext
    ext i j
    have e3 : ((reord π (R.eG (eR.symm (c⁻¹ * red k * c))) (plg kv) : GL (Fin D.R.r) (kP (plg kv).1)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (kP (plg kv).1)) i j =
        ((R.eG (eR.symm (c⁻¹ * red k * c)) (plg kv) : GL (Fin D.R.r) (kP (plg kv).1)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (kP (plg kv).1)) (π i) (π j) := by
      simp [reord, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
    rw [e3, e2]
    show (iso kv) ((((GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)))⁻¹ *
        ((P kv)⁻¹ * red k kv * P kv) * GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) (π i) (π j)) =
      (iso kv) (((((GlobalTheory.SeeConjRead.diagGL (d kv))⁻¹ * Ns kv * GlobalTheory.SeeConjRead.diagGL (d kv)) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i j)
    rw [GlobalTheory.SeeConjRead.diagGL_conj_apply, GlobalTheory.SeeConjRead.diagGL_conj_apply, hNs kv]
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  have hmemiff : reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H ↔
      ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k := by
    show _ ∈ Subgroup.pi Set.univ _ ↔ _
    rw [Subgroup.mem_pi]
    constructor
    · intro H kv
      have h1 := H (plg kv) (Set.mem_univ _)
      rw [hval kv, GlobalTheory.Mem.SymFrame.mem_unipSym_bc] at h1
      exact (GlobalTheory.SeeConjRead.unipSym_conj_iff _ _ _ _).2 h1
    · intro H PP _
      obtain ⟨kv, rfl⟩ := plg.surjective PP
      rw [hval kv, GlobalTheory.Mem.SymFrame.mem_unipSym_bc]
      exact (GlobalTheory.SeeConjRead.unipSym_conj_iff _ _ _ _).1 (H kv)
  have hK2 := GlobalTheory.T.mem_deeperLevel_iff_matrices_mod_place_symmetric D X h hpin hw k hk Ns hMat
  refine ⟨hK2.trans hmemiff.symm, fun hx => ?_⟩
  have hU := hmemiff.1 hx
  have hk2 : k ∈ X.K2 := hK2.2 hU
  rw [hchi k hk2 Ns hMat hU]
  have hchiv : (((PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨_, hx⟩ : ℂˣ) : ℂ) =
      ∏ PP : R.Pg, ψ0 PP.1 (edgeSum (symEdge D.R.rS D.R.k) (reord π (R.eG (eR.symm (c⁻¹ * red k * c))) PP)) := by
    unfold PsharpSym LevelP.ofLocal
    rw [MonoidHom.finset_prod_apply, Units.coe_prod]
    rfl
  rw [hchiv]
  refine (Fintype.prod_equiv plg _ _ (fun _ => rfl)).symm.trans (Finset.prod_congr rfl fun kv _ => ?_)
  rw [hval kv, GlobalTheory.Mem.SymFrame.edgeSum_bc, hd kv _ (hU kv)]
  rfl
