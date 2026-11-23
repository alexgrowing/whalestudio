import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.OptInEqSome
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts

noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7} (Λ : CutD D)

set_option maxHeartbeats 1600000

@[reducible] def nchTr (x : NChoice D) : NChoice (cut D Λ) := { x with }

@[reducible] def xdTr (x : ThData D) : ThData (cut D Λ) := { x with }

theorem nchTie_tr {x : NChoice D} (H : NChTie D x) : NChTie (cut D Λ) (nchTr Λ x) :=
  { H with
    twOf_eq := fun a => H.twOf_eq a.1
    twSide_eq := fun a => H.twSide_eq a.1
    Q_eq := fun a => H.Q_eq a.1
    psi_eq := H.psi_eq.imp fun _ k => ⟨k.1, k.2.1, fun a => k.2.2 a.1⟩ }

theorem sLen_tr (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ) (Q : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))) (ψ : BlochKatoReduction.Gen.GE D.nd →* (D.ntw.Ok i k)ˣ) :
    BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 (cut D Λ)) i s k Q ψ = BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) i s k Q ψ := by
  delta BlochKatoReduction.Gen.sLen BlochKatoReduction.Gen.selT BlochKatoReduction.Gen.bk BlochKatoReduction.Gen.Trep BlochKatoReduction.Gen.Tgl BlochKatoReduction.Gen.IsImgK BlochKatoReduction.Gen.IsFrac BlochKatoReduction.Gen.phiK BlochKatoReduction.Gen.chiS BlochKatoReduction.Gen.Spl BlochKatoReduction.bk0 BlochKatoReduction.Gen.PDv BlochKatoReduction.Gen.repV BlochKatoReduction.Gen.DecV BlochKatoReduction.Gen.GE
  dsimp +instances only [cut, GlobalTheory.HeightCounting.setRaw, GlobalTheory.HeightCounting.NLay0.reEta, layCut, ndCut, GlobalTheory.HeightCounting.rowsEta]
  congr 1

theorem twAt_tr {x : NChoice D} {y : ThData D} (H : LocalQuadraticParts.TWAt D x y) : LocalQuadraticParts.TWAt (cut D Λ) (nchTr Λ x) (xdTr Λ y) := by
  obtain ⟨hc, N0, S, H⟩ := H
  refine ⟨hc, N0, S, fun w hw => ⟨(H w hw).1, ?_⟩⟩
  obtain ⟨h1, h2, h3, ⟨e, h4, h4', h4''⟩, h5, h6⟩ := (H w hw).2
  exact ⟨h1, h2, h3, ⟨e, h4, h4', fun s hs => (sLen_tr Λ _ s _ _ _).trans_le (h4'' s hs)⟩, h5, h6⟩

end UpperTheory.GalC
