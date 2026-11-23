import Formalism.LocalRingCardinality.DataNChoice

noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

set_option synthInstance.maxHeartbeats 400000 in

structure NChTie (D : D7) (c : NChoice D) : Prop where

  twOf_eq : ∀ a : D.nd.Loc, D.ntw.twOf a = c.twI (D.nd.w a)

  twSide_eq : ∀ a : D.nd.Loc, D.ntw.twSide a = c.sd (D.nd.w a)

  Q_eq : ∀ a : D.nd.Loc, D.nd.Q a = c.Q (D.nd.w a)

  psi_eq : ∃ ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ),
    (∀ w, ψ0 (D.what₂.places.conj w) = ψ0 w) ∧
    (∀ w g, c.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) =
      algebraMap (c.Oe w) (FractionRing (c.Oe w)) (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
        ((c.psi' w (D.ntw.art (c.twI w) (c.Q w) g) : (D.ntw.Ok (c.twI w) (c.k' w))ˣ) : D.ntw.Ok (c.twI w) (c.k' w)))) ∧
    (∀ (a : D.nd.Loc) g, D.nd.embK a ((ψ0 (D.nd.w a) g : (D.what₂.LL)ˣ) : D.what₂.LL) =
      algebraMap (D.nd.O a) (FractionRing (D.nd.O a)) ((D.ntw.psiL a g : (D.nd.O a)ˣ) : D.nd.O a))

  embedding_baseField_condition : ∀ w (x : D.LL0) (y z : D.ntw.O0 (c.twI w)), z ≠ 0 →
    (if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x *
        algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) z =
      algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) y →
    c.embW w (x : D.what₂.LL) *
        algebraMap (c.Oe w) (FractionRing (c.Oe w)) (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
          (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z))) =
      algebraMap (c.Oe w) (FractionRing (c.Oe w)) (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
        (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y)))

structure ThData (D : D7) where
  xd0 : ∀ i j b, Set (D.nexp.Dat i j b)
  thetaBase_invariant_action : ∀ i j b, ∀ a ∈ xd0 i j b, ∀ u : D.nexp.U, D.nexp.actG i j b u (D.nexp.th i j b a) =
    ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • D.nexp.th i j b a

end Formalism.BasicNotions

end
