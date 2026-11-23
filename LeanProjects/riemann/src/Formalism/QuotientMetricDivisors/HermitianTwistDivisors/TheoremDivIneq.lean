import Mathlib
import Formalism.QuotientMetricDivisors.StatementK
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DivAssembly
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AbsorbE

open Finset

noncomputable section

namespace Formalism.DivisionValues

theorem divisor_inequality : TheoremDivIneq := by
  intro J Pl _ _ TT _ muC mu0 Fo hu hP mlam logT hK aT phν nν fa x eps L b a rd La B0 Nc xe m f k N S
    tt η w'' b' dC lam0 C0 Lpass Eb e6 eP logOm eK pq w eE δ
    h1 h2 h3 h4 h5 h6 h7 h8
    hx heps hL hb ha hrd1 hlogrd hlogx hLa hB0 hNc hxeb hJ hPl hm hf hk hN hS ht hη hdC
    hw hpq hOm hlam hNd hm3 hmηN hkN hkS hmt hNw hb'N hmkb' hC0 hLp hEb heK he6 heP heE hδ
  have hD := divisor_inequality_assembly J Pl TT muC mu0 Lpass 0 Fo Eb hu hP mlam e6 eP logOm logT k hK eK pq aT
    w phν nν fa eE δ h1 (by linarith) (by linarith) h4 h5 h6 h7 h8
  have hA := error_absorption J Pl TT x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' dC lam0 C0 Lpass
    Eb e6 eP logOm k eK pq w eE δ hx heps hL hb ha hrd1 hlogrd hlogx hLa hB0 hNc hxeb hJ hPl hm hf hk
    hN hS ht hη hdC hw hpq hOm hlam hNd hm3 hmηN hkN hkS hmt hNw hb'N hmkb' hC0 hLp hEb heK he6 heP
    heE hδ
  rw [hJ] at hD
  linarith

end Formalism.DivisionValues
