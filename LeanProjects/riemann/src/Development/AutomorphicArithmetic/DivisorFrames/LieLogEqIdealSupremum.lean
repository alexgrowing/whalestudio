import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.DualNumberTangentCoordinates
import Development.AutomorphicArithmetic.DivisorFrames.PadicCoordinateInfimum
import Development.AutomorphicArithmetic.DivisorFrames.LieLatticeGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead

private theorem mem_letters'' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (x : Letter Dw) : x ∈ letters Dw := by
  obtain ⟨τ, i⟩ := x
  obtain ⟨a, rfl⟩ := (Fintype.equivFin (E →+* ℂ)).symm.surjective τ
  unfold letters
  exact List.mem_flatMap.2 ⟨a, List.mem_finRange _, List.mem_map.2 ⟨i, List.mem_finRange _, rfl⟩⟩

private theorem nodup_letters'' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) : (letters Dw).Nodup := by
  unfold letters
  rw [List.nodup_flatMap]
  refine ⟨fun a _ => (List.nodup_finRange _).map fun i j h => ?_, ?_⟩
  · exact eq_of_heq (Sigma.mk.inj_iff.1 h).2
  · refine (List.nodup_finRange _).imp ?_
    intro a b hab
    simp only [Function.onFun]
    intro x hx hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, -, h⟩ := List.mem_map.1 hy
    exact hab ((Fintype.equivFin (E →+* ℂ)).symm.injective (congrArg Sigma.fst h)).symm

private theorem grNorm_sub {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (x : Sp C ⟶ X)
    {m g : ℕ} (e : Fin m → Fin g) (he : Function.Injective e) (U : Fin g → (Sp (DualNumber C) ⟶ t.G.left))
    (hU : ∀ k, IsTanAtG t x (U k)) (u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)) (hu : ∀ a, u a = U (e a))
    (Λ : Set (Sp (DualNumber C) ⟶ t.G.left)) (P : (Fin g → C) → Prop)
    (hP : ∀ c w, IsCombAtG t x U c w → (w ∈ Λ ↔ P c)) (i : Fin m) (S : Set (Fin g))
    (hS : ∀ k, k ∈ S ↔ ∃ a, a ≤ i ∧ e a = k) :
    grNorm t x Λ u i = sInf {r : ℝ | ∃ c : Fin g → C, c (e i) ≠ 0 ∧ (∀ k, k ∉ S → c k = 0) ∧ P c ∧ r = ‖c (e i)‖⁻¹} := by
  classical
  let A : Matrix (Fin g) (Fin m) C := fun j a => (Pi.single (e a) 1 : Fin g → C) j
  have hA : ∀ a, IsCombAtG t x U (fun j => A j a) (u a) := fun a => by
    rw [hu]; exact isCombAtG_single t x hU (e a)
  have h1 : ∀ cf a, A.mulVec cf (e a) = cf a := fun cf a => by
    simp [A, Matrix.mulVec, dotProduct, Pi.single_apply, he.eq_iff]
  have h2 : ∀ cf k, (∀ a, e a ≠ k) → A.mulVec cf k = 0 := fun cf k hk => by
    simp [A, Matrix.mulVec, dotProduct, Pi.single_apply, fun a => (hk a).symm]
  have hu' : ∀ a, IsTanAtG t x (u a) := fun a => hu a ▸ hU _
  unfold grNorm
  congr 1
  ext r
  constructor
  · rintro ⟨cf, h0, hz, ⟨w, hw, hc⟩, rfl⟩
    refine ⟨A.mulVec cf, by rwa [h1], fun k hk => ?_, (hP _ w (tanLinG U hU u A cf w hA hc)).1 hw, by rw [h1]⟩
    by_cases hk' : ∃ a, e a = k
    · obtain ⟨a, rfl⟩ := hk'
      rw [h1]
      exact hz a (lt_of_not_ge fun h => hk ((hS _).2 ⟨a, h, rfl⟩))
    · exact h2 cf k fun a ha => hk' ⟨a, ha⟩
  · rintro ⟨c, h0, hz, hc, rfl⟩
    obtain ⟨w, -, hw⟩ := GlobalTheory.FlagEmb.exists_comb t hu' fun a => c (e a)
    have e1 : A.mulVec (fun a => c (e a)) = c := by
      funext k
      by_cases hk' : ∃ a, e a = k
      · obtain ⟨a, rfl⟩ := hk'
        rw [h1]
      · rw [h2 _ k fun a ha => hk' ⟨a, ha⟩, hz k]
        intro hk
        obtain ⟨a, -, ha⟩ := (hS k).1 hk
        exact hk' ⟨a, ha⟩
    have h3 := tanLinG U hU u A _ w hA hw
    rw [e1] at h3
    refine ⟨fun a => c (e a), h0, fun a ha => hz _ fun hk => ?_, ⟨w, (hP c w h3).2 hc, hw⟩, rfl⟩
    obtain ⟨b, hb, hb'⟩ := (hS _).1 hk
    rw [he hb'] at hb
    exact absurd ha (not_lt.2 hb)

theorem UpperTheory.lie_log_eq_ideal_supremum :
    ∀ (D : D7) (O : Setup D) (y : Pt O.s) (K : Type) [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb), FibTie O y F ι → ∀ (p : ℕ) [Fact p.Prime] (io : Qb →+* ℂ_[p]) (τ : D.host.E →+* ℂ) (i : ℕ), i < O.S.Dw.mult τ → y.lnLie io p false τ i = -Real.log (sSup ((fun b => ‖io (ι b)‖) '' (stepIdeal O F τ i : Set K))) := by
  intro D O y K _ _ F ι hT p _ io τ i hi
  have hg : F.P₀.g = (letters O.S.Dw).length := by
    obtain ⟨_, _, _, -, -, -, -, hg, -⟩ := hT
    exact hg
  obtain ⟨q, hq, -, -, hex, hI⟩ := UpperTheory.lie_lattice_generator D O K F τ i hi hg
  have hlt : ∀ k : Fin F.P₀.g, (k : ℕ) < (letters O.S.Dw).length := fun k => hg ▸ k.2
  let l : Fin F.P₀.g → Letter O.S.Dw := fun k => (letters O.S.Dw)[(k : ℕ)]'(hlt k)
  have hl : ∀ (k : Fin F.P₀.g) x, (letters O.S.Dw)[(k : ℕ)]? = some x ↔ l k = x := fun k x => by
    rw [List.getElem?_eq_getElem (hlt k), Option.some_inj]
  have linj : Function.Injective l := fun a b h =>
    Fin.ext ((List.Nodup.getElem_inj_iff (nodup_letters'' O.S.Dw)).1 h)
  have hsurj : ∀ x, ∃ k, l k = x := fun x => by
    obtain ⟨n, hn, h⟩ := List.getElem_of_mem (mem_letters'' O.S.Dw x)
    exact ⟨⟨n, hg ▸ hn⟩, h⟩
  choose pl hpl using hsurj
  let e : Fin (O.S.Dw.mult τ) → Fin F.P₀.g := fun a => pl ⟨τ, a⟩
  have he : Function.Injective e := fun a b h => by
    have := (hpl ⟨τ, a⟩).symm.trans ((congrArg l h).trans (hpl ⟨τ, b⟩))
    exact eq_of_heq (Sigma.mk.inj_iff.1 this).2
  have hqe : q = e ⟨i, hi⟩ := linj (((hl _ _).1 hq).trans (hpl _).symm)
  let U : Fin F.P₀.g → (Sp (DualNumber ℂ_[p]) ⟶ O.s.T.Z.t.G.left) :=
    fun k => spMap (dualMap io) ≫ y.u (l k).1 (l k).2
  have hU : ∀ (k : Fin F.P₀.g) (x : Letter O.S.Dw), (letters O.S.Dw)[(k : ℕ)]? = some x →
      U k = spMap (dualMap io) ≫ y.u x.1 x.2 := fun k x h => by
    rw [← (hl k x).1 h]
  have key := grNorm_sub O.s.T.Z.t (spMap io ≫ y.y ≫ genι O.s.T.Z) e he U
    (fun k => GlobalTheory.FactorDepth.isTanAtG_map _ io (y.tan _ _)) (fun a => spMap (dualMap io) ≫ y.u τ a)
    (fun a => (hU _ ⟨τ, a⟩ ((hl _ _).2 (hpl _))).symm) _ _ (UpperTheory.dual_number_tangent_coordinates D O y K F ι hT p io U hU) ⟨i, hi⟩
    {k : Fin F.P₀.g | ∃ x : Letter O.S.Dw, x.1 = τ ∧ (x.2 : ℕ) < i + 1 ∧ (letters O.S.Dw)[(k : ℕ)]? = some x}
    (fun k => by
      constructor
      · rintro ⟨⟨τ', a⟩, h1, h2, h3⟩
        dsimp only at h1 h2
        subst h1
        exact ⟨a, Nat.lt_succ_iff.1 h2, linj ((hpl _).trans ((hl _ _).1 h3).symm)⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨τ, a⟩, rfl, Nat.lt_succ_iff.2 ha, (hl _ _).2 (hpl _)⟩)
  have h2 := UpperTheory.padic_coordinate_infimum p K _ (io.comp ι) F.lieLat _ q (GlobalTheory.T.semi_fibration_lie_lattice_full K F).1.1 hex
  rw [← hqe] at key
  rw [hI, ← Real.log_inv]
  unfold FlagPt.lnLie
  rw [dif_pos hi]
  exact congrArg Real.log (key.trans h2)
