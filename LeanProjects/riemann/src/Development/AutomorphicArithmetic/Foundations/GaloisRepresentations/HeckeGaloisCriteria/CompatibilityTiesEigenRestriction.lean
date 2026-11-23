import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.OptInEqSome

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Alg

def descHom {O X M B : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Semiring B] [Algebra O B]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M) (S : Set X) (z : B →ₐ[O] Module.End O M)
    (h : ∀ b (f : T), z b * act f = act f * z b) : B →ₐ[O] Module.End O (cutM T act S) where
  toFun b := desc T act S (z b) (h b)
  map_one' := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [desc_mk, map_one]; rfl
  map_mul' a b := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [Module.End.mul_apply, desc_mk, desc_mk, desc_mk, map_mul]; rfl
  map_zero' := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [desc_mk, map_zero]; rfl
  map_add' a b := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [LinearMap.add_apply, desc_mk, desc_mk, desc_mk, map_add, LinearMap.add_apply, map_add]
  commutes' a := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [desc_mk, AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]

variable {D : D7} (c : CutD D)

def zCut (Q : PairedCharacterCondition.Pend D) (i : D.nd.Loc) (S : Set (D.nd.X i)) :
    ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) →ₐ[D.nd.O i]
      Module.End (D.nd.O i) (cutM (D.nd.T i) (D.nd.act i) S) :=
  descHom (D.nd.T i) (D.nd.act i) S (Q.zO i) (Q.zO_comm i)

set_option maxHeartbeats 2000000 in

def pendCut (Q : PairedCharacterCondition.Pend D) : PairedCharacterCondition.Pend (cut D c) where
  lz := Q.lz
  eSer_eq := Q.eSer_eq
  eSer_LL := Q.eSer_LL
  zetaPrimitiveRoot := fun i => Q.zetaPrimitiveRoot i.1
  om := Q.om
  om_one := Q.om_one
  om_mul := Q.om_mul
  tameInertiaChar_mul_root := Q.tameInertiaChar_mul_root
  om_wild := Q.om_wild
  om_open := Q.om_open
  om_inj := Q.om_inj
  om_tg := Q.om_tg
  inertiaCharpoly_eigenvalues := Q.inertiaCharpoly_eigenvalues
  inertiaCharpoly_character := Q.inertiaCharpoly_character
  zO := fun i => zCut Q i.1 (c.Xs i.1)
  zO_comm := fun i z f => desc_comm (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) _ (Q.zO_comm i.1 z) f
  zL_stable := fun i => Q.zL_stable i.1
  zO_act := fun i z x y h =>
    (congrArg (qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1)) (Q.zO_act i.1 z x y h)).trans
      (qK_desc (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) _ (Q.zO_comm i.1 z) _).symm
  prMt_type := fun i PI x hx => by
    obtain ⟨a, b⟩ := Q.prMt_type i.1 PI x hx
    refine ⟨fun p hp => qK_mem (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (x := p) (a p.1 (optIn_eq_some.1 hp)), fun hn => ?_⟩
    show qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (D.nd.prMt i.1 x) = 0
    cases hp : D.naut.ptV i.1 PI with
    | none => rw [b hp, map_zero]
    | some p =>
      refine qK_out (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (D.nd.T_sep i.1) (x := p) (fun hm => ?_) (a p hp)
      have := (optIn_eq_some (S := c.Xs i.1) (x := ⟨p, hm⟩)).2 hp
      exact Option.some_ne_none _ (this.symm.trans hn)
  Par_surj := fun i x Sig h => Q.Par_surj i.1 x.1 Sig (h.imp fun _ k => ⟨optIn_eq_some.1 k.1, k.2⟩)
  kty := fun i => Q.kty i.1
  kty_spec := fun i => Q.kty_spec i.1

theorem eigSpan_cut {Q : PairedCharacterCondition.Pend D} (h : GlobalTheory.Pass.EigSpan Q) : GlobalTheory.Pass.EigSpan (pendCut c Q) := by
  intro i z x a ha u hu
  have hu' : u ∈ (heckeEig (D.nd.T i.1) (D.nd.act i.1) x.1).map (qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1)) := by
    rw [map_eig _ _ _ (D.nd.T_sep i.1) x]; exact hu
  obtain ⟨v, hv, rfl⟩ := hu'
  have e := h i.1 z x.1 a (fun PI hP => ha PI (optIn_eq_some.2 hP)) v hv
  refine (qK_desc (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) _ (Q.zO_comm i.1 z) v).trans ?_
  rw [e]
  have k : ∀ (b : D.nd.O i.1) (w : TensorProduct (D.nd.O i.1) (FractionRing (D.nd.O i.1)) (D.nd.Mt i.1)),
      qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (b • w) = b • qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) w := fun b w => by
    rw [← algebraMap_smul (FractionRing (D.nd.O i.1)) b w, map_smul, algebraMap_smul]
  exact k a v

theorem compatibilityTies_eigenRestriction (h : Tie4 D) : Tie4 (cut D c) := by
  obtain ⟨a, ⟨Q, hDZ, hE⟩, b, d⟩ := h
  exact ⟨fun i => a i.1, ⟨pendCut c Q, fun i => hDZ i.1, eigSpan_cut c hE⟩, fun i => b i.1, fun i => d i.1⟩

end UpperTheory.GalC
