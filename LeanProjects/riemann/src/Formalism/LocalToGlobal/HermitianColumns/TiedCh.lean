import Formalism.LocalToGlobal.HermitianColumns.HermCols

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure HermColsCh (D : D7) where

  lev0 : LevelData D

  Ch : D.what₂.Word → ℕ → Type
  [ChFin : ∀ u i, Finite (Ch u i)]

  Ch_m : ∀ u, Nonempty (Unique (Ch u D.R.m))

  chOf : ∀ u i, (D.mem u).C.cls i → Ch u i

  lev : ∀ (u : D.what₂.Word) (i : ℕ), 1 ≤ i → i ≤ D.R.m → Ch u i →
    StepLevel D.sp.cm (D.sp.X i) D.host.g (D.mem u).A.T D.R.f

  cls : ∀ (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : Ch u i),
    ClassTie D.sp.cm (D.sp.X i) (lev u i h1 hm β).Lb (lev u i h1 hm β).U
      (fun c : {c // chOf u i c = β} => (D.mem u).C.stab i c.1) (fun c => D.clsLat u i c.1)

  vT : ∀ u : D.what₂.Word, (D.mem u).A.vT ≃
    {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}

  Fv : ∀ (u : D.what₂.Word) (v : (D.mem u).A.vT), (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (vT u v).1.asIdeal)

attribute [instance] HermColsCh.ChFin

end Formalism.L2.Herm

end
