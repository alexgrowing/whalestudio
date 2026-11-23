import Formalism.LocalToGlobal.HermitianForms.TiedTwSame
import Formalism.LocalToGlobal.HermitianForms.TiedTwJ
import Formalism.LocalToGlobal.HermitianColumns.TiedQCHost

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG

namespace Formalism.L2.Forms

variable {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

theorem TwFormsTied.Fi_zero {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {F : ∀ u, FormsTied D u} (W : TwFormsTied D Tw T F)
    (u : D.what₂.Word) (μ : D.what₂.Tup) :
    (Tw.fm u μ).Fi 0 = ((D.fm u).Fi 0).map (D.e0Tw u μ : _ →ₗ[ℂ] _) := by
  rw [(Tw.fm u μ).Fi_zero, (D.fm u).Fi_zero, (W.atT u μ).Mu0]

theorem twisted_embedding_level_zero (Tw : TwForms D) (T : Formalism.L2.Herm.TwChTied D inQ) (u : D.what₂.Word) (μ : D.what₂.Tup) (x : ((D.fm u).lat 0).V)
    (c : (D.mem u).C.cls 0) (y : (D.mem u).C.Y 0) :
    (Tw.fm u μ).emb 0 (Tw.e0 u μ x) (T.eCls0 u μ c) (T.eY u μ 0 (Nat.zero_le _) y) = (D.fm u).emb 0 x c y := by
  rw [Tw.embed_mul_block_embedding, T.twisted_character_eq]

theorem twisted_embedding_frames (Tw : TwForms D) (T : Formalism.L2.Herm.TwChTied D inQ) (F : ∀ u, FormsTied D u) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) (z : Fr D 0 (Nat.zero_le _)) :
    (Tw.fm u μ).emb 0 (Tw.e0 u μ x) (T.eCls0 u μ c) ((twY T F u μ 0 (Nat.zero_le _)).symm z) =
      (D.fm u).emb 0 x c (((F u).val 0 (Nat.zero_le _)).eY.symm z) :=
  twisted_embedding_level_zero Tw T u μ x c _

theorem lamTG_tw (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j ≤ D.R.m) :
    lamTG (Tw.fm u μ) j = lamT u j := by
  unfold lamTG lamT
  rw [lam_tw Tw u μ j hj]

structure TwistedColumnsCompatible {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} (tp : Formalism.L2.Host.TupTied D cf nch)
    (cols : ColsTied D) (Tw : TwForms D) where
  ch : Formalism.L2.Herm.TwistedCharacterData tp
  chJ : Formalism.L2.Herm.TwChJoint ch cols.herm.base
  chM : Formalism.L2.Herm.TwChMu0 ch
  forms : TwFormsTied D Tw ch cols.forms
  lv : TwistedLevelData forms

  same : TwLvSame forms

  lvJ : TwistedJointForms ch cols.forms

end Formalism.L2.Forms

end
