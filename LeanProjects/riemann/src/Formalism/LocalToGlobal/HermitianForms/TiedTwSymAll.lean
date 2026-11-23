import Formalism.LocalToGlobal.HermitianForms.TiedTwSymP
import Formalism.LocalToGlobal.HermitianColumns.TiedQCHost

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.Formalism.L2.Herm.TwChJointS.Uloc_g {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}
    {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} (J : Formalism.L2.Herm.TwChJointS T H) (u : D.what₂.Word)
    (μ : D.what₂.Tup) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) (v : HeightOneSpectrum (𝓞 D.host.F)) (a : Fin 2)
    (hv : (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal) (hi : i + 1 ≠ D.R.m) :
    (T.lev u μ i h1 hm β).Uloc v = (H.lev u i h1 hm (J.gOf u μ i β)).Uloc v :=
  J.Uloc_off u μ i h1 hm β v (fun hQ => (J.Q_off u μ v hQ).2 a hv) (Or.inl hi)

structure SymmetricTwistedColumnsCompatible {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} (tp : Formalism.L2.Host.TupTied D cf nch)
    (cols : ColsTiedSym D) (Tw : TwForms D) where
  ch : Formalism.L2.Herm.TwistedCharacterData tp
  chJ : Formalism.L2.Herm.TwChJointS ch cols.herm.base
  chM : Formalism.L2.Herm.TwChMu0 ch
  forms : TwFormsTiedS D Tw ch chJ cols.forms
  lv : SymmetricTwistedLevelData forms

  same : TwLvSameS forms

  lvJ : SymmetricTwistedJointForms ch cols.forms

structure SymmetricTwistedColumnsAtPrimes {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} (tp : Formalism.L2.Host.TupTied D cf nch)
    (cols : ColsTiedSym D) (Tw : TwForms D) extends SymmetricTwistedColumnsCompatible tp cols Tw where

  pt : TwPTiedS lv

  ptG : TwPAtGS pt

  ptE : TwPEvzS pt

end Formalism.L2.Forms

end
