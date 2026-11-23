import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import GroundTheory.GlobalFields.Adele.Compact

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LastRowIntegral

open ValuativeRel

theorem mul_apply_last {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (i : Fin n)
    (hi : (i : ℕ) + 1 = n) (h0 : ∀ j, j < i → A i j = 0) (h1 : A i i = 1) (c : Fin n) : (A * B) i c = B i c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [h1, one_mul]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [h0 j h, zero_mul]
    · exfalso
      have h2 := j.isLt
      have h3 : (i : ℕ) < j := h
      omega
  · intro h; exact absurd (Finset.mem_univ i) h

variable {E : Type} [Field E] [NumberField E]

theorem lastRow_eq {k : ℕ} (hk : 1 ≤ k) (g : GA E k) (c : Fin k) :
    lastRow g c = g.val ⟨k - 1, by omega⟩ c := by
  unfold lastRow
  rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
  · rw [if_pos (by simp only; omega)]
  · intro j _ hj
    rw [if_neg]
    intro h; apply hj; ext; simp only; omega
  · intro h; exact absurd (Finset.mem_univ _) h

theorem lastRow_UU {k : ℕ} (hk : 1 ≤ k) {n : GA E k} (hn : UU 0 n) (g : GA E k) :
    lastRow (n * g) = lastRow g := by
  funext c
  rw [lastRow_eq hk, lastRow_eq hk, Units.val_mul]
  refine mul_apply_last _ _ _ (by simp only; omega) (fun j hj => hn.1 _ _ hj) (hn.2.1 _) c

theorem continuous_lastRow {k : ℕ} : Continuous (lastRow : GA E k → Fin k → Ad E) := by
  refine continuous_pi fun c => continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact Units.continuous_val.matrix_elem i c
  · exact continuous_const

theorem continuous_sFin : Continuous (sFin E) :=
  (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))

theorem mem_int (w : Pl E) (x : w.adicCompletion E) (hx : x ∈ 𝒪[w.adicCompletion E]) :
    x ∈ w.adicCompletionIntegers E := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hO : 𝒪[w.adicCompletion E] = (w.adicCompletionIntegers E).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  rw [hO] at hx
  exact hx

end LastRowIntegral

namespace LastRowIntegral

open ValuativeRel GroundTheory.Automorphic.Iwasawa

theorem last_int {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) (ιw : GL (Fin k) F →* GL (Fin m) F)
    (hu : ∀ n ∈ unipotent F k, ιw n ∈ unipotent F m)
    (hκ : ∀ κ ∈ GLnLocal.integralGL F k, ιw κ ∈ GLnLocal.integralGL F m)
    (ht : ∀ l, ιw (torusPow F k l) = torusPow F m (pad m l)) (h : GL (Fin k) F)
    (ha : Antitone (iwasawaExponent F m (ιw h))) (c : Fin k) : h ⟨k - 1, by omega⟩ c ∈ 𝒪[F] := by
  obtain ⟨u, hu0, κ, hκ0, he⟩ := exists_eq_mul_torusPow_iwasawaExponent F k h
  set l := iwasawaExponent F k h
  have hl : iwasawaExponent F m (ιw h) = pad m l := by
    rw [he, map_mul, map_mul, ht]
    exact iwasawaExponent_eq F m (hu u hu0) (hκ κ hκ0)
  rw [hl] at ha
  have h0 : 0 ≤ l ⟨k - 1, by omega⟩ := by
    have := ha (show (⟨k - 1, by omega⟩ : Fin m) ≤ ⟨k, hkm⟩ from Fin.mk_le_mk.2 (by omega))
    simpa [pad, show k - 1 < k by omega] using this
  obtain ⟨e, he'⟩ := Int.eq_ofNat_of_zero_le h0
  rw [he, Units.val_mul, Units.val_mul, Matrix.mul_assoc,
    mul_apply_last _ _ _ (by simp only; omega) (fun j hj => hu0.1 hj) (hu0.2 _) c, coe_torusPow,
    Matrix.diagonal_mul, he', zpow_natCast]
  exact Subring.mul_mem _ (Subring.pow_mem _ (GLnLocal.uniformizer F).2 _)
    (((GLnLocal.mem_integralGL_iff F k).1 hκ0).1 _ _)

end LastRowIntegral

theorem last_row_integral_of : jumpWindows.G0 → CornerEmbedding → K8 → K6 := by
  intro hG0 h5 h8 E _ _ _ m k hk hkm ψ hψ S hS ι hι α M U φ hP
  obtain ⟨hex, hι5⟩ := h5 E m k hkm.le
  obtain ⟨-, hblk, hsurj, -, -, hcpt, -, hloc, hcInf, hUU, -⟩ := hι5 ι hι
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hg0, -, -, -, -⟩ := hG0 E k
  obtain ⟨-, -, hW⟩ := h8 E m ψ hψ S hS α φ hP.good hP.sat
  obtain ⟨C, -, hCblk, hCcpt, -, -, hB⟩ := hP.bump
  choose ιw hιw using fun w : Pl E => hex (w.adicCompletion E)
  have hlw := fun w => hloc w (ιw w) (hιw w)
  refine ⟨(fun p => p.1 + p.2) '' ((lastRow '' (ι ⁻¹' C)) ×ˢ
    Set.pi Set.univ (fun _ => sFin E '' (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)))), ?_, ?_⟩
  · exact (((hcpt C hCcpt).image LastRowIntegral.continuous_lastRow).prod (isCompact_univ_pi fun _ =>
      (GroundTheory.Global.isCompact_integralFiniteAdeles E).image LastRowIntegral.continuous_sFin)).image
      (continuous_fst.add continuous_snd)
  intro g hg
  obtain ⟨hW1, hW2⟩ := hW (ι g) hg
  obtain ⟨g₀, h0i, h0S, h0in⟩ := hg0 S g
  have hinf : cInf (ι g₀) = cInf (ι g) := by
    have e : g = g₀ * (g₀⁻¹ * g) := by group
    have h1 : cInf (g₀⁻¹ * g) = 1 := by rw [map_mul, map_inv, h0i, inv_mul_cancel]
    conv_rhs => rw [e, map_mul, map_mul, hcInf _ h1, mul_one]
  have hSl : ∀ w ∈ S, cLoc w (ι g₀) = cLoc w (ι g) := fun w hw => by
    rw [(hlw w).2.1, (hlw w).2.1, h0S w hw]
  have hin : InS S (ι g₀) := fun w hw => by rw [(hlw w).2.1, h0in w hw, map_one]
  have hne := hW1 (ι g₀) hinf hSl hin
  have hmir : Mir k (ι g₀) := fun i c h => hblk g₀ i c (h.imp id Nat.le_of_lt)
  obtain ⟨n, c, hc, t, hn, -, heq, -, -⟩ := hB (ι g₀) ⟨hin, hmir⟩ hne
  obtain ⟨c', rfl⟩ := hsurj c (hCblk c hc)
  have hn' : n = ι (g₀ * c'⁻¹) := by rw [map_mul, map_inv, heq, mul_inv_cancel_right]
  have hU0 : UU 0 (g₀ * c'⁻¹) := (hUU _).1 (hn' ▸ hn)
  have hA : lastRow g₀ = lastRow c' := by
    conv_lhs => rw [show g₀ = (g₀ * c'⁻¹) * c' by group]
    exact LastRowIntegral.lastRow_UU hk hU0 c'
  refine ⟨(lastRow g₀, lastRow g - lastRow g₀), ⟨⟨c', hc, hA.symm⟩, fun i _ => ?_⟩, by simp⟩
  refine ⟨pFin E ((lastRow g - lastRow g₀) i), ?_, ?_⟩
  · intro v
    change pLoc E v (pFin E ((lastRow g - lastRow g₀) i)) ∈ v.adicCompletionIntegers E
    rw [Pi.sub_apply, LastRowIntegral.lastRow_eq hk, LastRowIntegral.lastRow_eq hk, map_sub, map_sub]
    change (cLoc v g).val _ i - (cLoc v g₀).val _ i ∈ v.adicCompletionIntegers E
    by_cases hv : v ∈ S
    · rw [h0S v hv, sub_self]; exact zero_mem _
    · rw [h0in v hv]
      refine sub_mem (LastRowIntegral.mem_int v _ ?_) (LastRowIntegral.mem_int v _ ?_)
      · have ha := hW2 v hv
        rw [(hlw v).2.1] at ha
        exact LastRowIntegral.last_int hk hkm (ιw v) (hlw v).2.2.1 (hlw v).2.2.2.1 (hlw v).2.2.2.2 _ ha i
      · change (1 : Matrix (Fin k) (Fin k) (v.adicCompletion E)) _ i ∈ _
        rw [Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
  · refine ad_ext ?_ rfl
    change (infEq E).symm 0 = _
    rw [map_zero]
    change (0 : Cinf E) = pInf E ((lastRow g - lastRow g₀) i)
    rw [Pi.sub_apply, LastRowIntegral.lastRow_eq hk, LastRowIntegral.lastRow_eq hk, map_sub]
    change (0 : Cinf E) = (cInf g).val _ i - (cInf g₀).val _ i
    rw [h0i, sub_self]

end PositivityTheory.AdelicQuotientData

end
