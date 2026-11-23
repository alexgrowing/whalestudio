import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AutomorphicArithmetic.DivisorFrames.ExistsAdaptedFlagCharts
import Development.AutomorphicArithmetic.DivisorFrames.ChartFrameDivisor
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

theorem UpperTheory.true_model_chart_divisor :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (N : GlobalTheory.TrueGeo.Model C.Y) (τ : E →+* ℂ) (M : N.X.Modules) (dual : Bool) (A : Chart M (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) C.Y.Fn) (fl : Vert.Flag M (Dw.mult τ)) (i : Fin (Dw.mult τ)) (s : ((fl.root i).pull N.j).ι → C.Y.Fnˣ) (kind : ℕ → Bool) (Ro : Option ℝ) (w : Pad.Sym E →₀ ℤ), w = Finsupp.single (kind, Ro, Sum.inl (τ, (pos dual i : ℕ))) (cond dual (-1) 1) → IsLie C.f0 τ N.j dual A → IsFlag (genericPt C.Y ≫ N.j) dual A fl → IsGrSec N.j dual A fl i s → ∀ k, ∀ y ∈ ((fl.root i).pull N.j).U k, (divOf C (expo Dw w)).IsEqn y (s k) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e C N τ M dual A fl i s kind Ro w hw hL hF hG k y hy
  classical
  obtain ⟨ch, hch, had⟩ := (UpperTheory.exists_adapted_flag_charts _ M _ fl).1 (N.j y)
  obtain ⟨t₀, ht₀⟩ := had i
  have hfr := (UpperTheory.exists_adapted_flag_charts _ M _ fl).2 ch had i t₀ ht₀
  have h1 := hG.2 ch had (gen_le N.j hch) t₀ ht₀ hfr
  obtain ⟨φ, f, t, hT, hE⟩ := C.gr_spec y
  obtain ⟨φ', f', hf'⟩ := hL.2 ch y hch
  have hφ : φ = φ' := RingHom.ext fun a => toFn_injective y
    ((RingHom.congr_fun hT.2.1 a).symm.trans (RingHom.congr_fun hf'.1 a))
  subst hφ
  obtain ⟨hu, h2⟩ := (UpperTheory.chart_frame_divisor E H Dw l Xo c O β Z F e C τ _ N.j M dual A fl hL hF ch had y hch φ f f' t hT hf').2 i
  have hd : divOf C (expo Dw w) = (cond dual (-1) 1 : ℤ) • C.gr τ (pos dual i) := by
    let x : Letter Dw := ⟨τ, pos dual i⟩
    have h : letterOf Dw (.inl (τ, (pos dual i : ℕ))) = some x := dif_pos x.2.2
    rw [hw, divOf, Finset.sum_eq_single x]
    · simp [expo, h, x]
    · intro y _ hy
      simp [expo, h, hy.symm]
    · simp
  have h3 := (hE τ (pos dual i)).zsmul (cond dual (-1) 1 : ℤ)
  rw [hd]
  have h4 := hG.1.germOf_eq (i := k) (j := fun _ => (⟨ch.U, _, hfr⟩ : Chart (fl.gr i) 1)) (x := y) hy (by
    exact Set.mem_iInter.2 fun _ => hch)
  unfold CartierDiv.IsEqn at h3 ⊢
  rw [h3, ← h4, eq_comm, germOf_eq_iff, div_eq_mul_inv, ← eq_inv_of_mul_eq_one_right h1, mul_comm, h2]
  exact ⟨_, hu, rfl⟩
