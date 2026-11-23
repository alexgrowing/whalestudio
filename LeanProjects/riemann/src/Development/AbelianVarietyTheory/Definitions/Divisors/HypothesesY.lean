import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd

namespace GlobalTheory.CovHt

structure HypothesesY : Prop where

  alt : GlobalTheory.Published.RegularAlteration

  dem : GlobalTheory.Published.DemaillyRegularisation

  mat : GlobalTheory.Published.MatrixLemma

  sieg : GlobalTheory.Published.AbsoluteSiegel

  perfd : GlobalTheory.Published.PrismaticDieudonnePerfd

example (h : HypothesesY) : GlobalTheory.Published.RegularAlteration ∧ GlobalTheory.Published.PrismaticDieudonnePerfd := ⟨h.alt, h.perfd⟩

end GlobalTheory.CovHt
