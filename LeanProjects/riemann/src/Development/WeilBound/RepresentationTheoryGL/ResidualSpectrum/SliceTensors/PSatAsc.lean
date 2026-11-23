import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatCore
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatTw
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.EventuallySatV
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasSatGLLocRep
import GroundTheory.PAdicHodge.AInfGalois

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs

namespace satakeAscent

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem eventually_spherical {a : ℕ} (π : CuspSub E a) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      GlobalTheory.LGrp.IsSpherical (π.locRep w) (GlobalTheory.LFun.KGL w a) := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  filter_upwards [LocSph.eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))] with w hw
  refine (Submodule.ne_bot_iff _).2 ⟨⟨φ, hφ⟩, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, fun e => h0 (congrArg Subtype.val e)⟩
  obtain ⟨g, rfl⟩ := hk
  exact Subtype.ext (hw g)

theorem satLike_cusp {m : ℕ} (π' : CuspSub E m) {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : GlobalTheory.LFun.HasSatGL w (π'.locRep w) B) : SatakeVectors.SatLike π'.V w B := fun ψ hψ hK h0 => by
  have hx := h.2 ⟨ψ, hψ⟩ (GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (hK k hk))
    fun e => h0 (congrArg Subtype.val e)
  exact hx.map (ρ' := (finRep E m).comp (locGL E m w)) π'.V.subtype (fun _ _ => rfl) h0

theorem modExp_const {a d : ℕ} (i : Fin d) :
    modExp (fun _ : Fin d => Fin a) i = (a : ℤ) * ((d : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) := by
  have e : modExp (fun _ : Fin d => Fin a) i =
      (∑ _b ∈ Finset.Ioi i, (a : ℤ)) - ∑ _b ∈ Finset.Iio i, (a : ℤ) := by
    unfold modExp
    congr 1
    · exact Finset.sum_congr (by ext; simp) fun _ _ => by simp
    · exact Finset.sum_congr (by ext; simp) fun _ _ => by simp
  have hi := i.2
  have hc : ((d - 1 - (i : ℕ) : ℕ) : ℤ) = (d : ℤ) - 1 - ((i : ℕ) : ℤ) := by omega
  rw [e, Finset.sum_const, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio, nsmul_eq_mul, nsmul_eq_mul, hc]
  ring

theorem spehExp_rev (d : ℕ) (i : Fin d) : spehExp d i.rev = -spehExp d i := by
  have h := i.2
  simp only [spehExp, Fin.val_rev]
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem term_eq {a d : ℕ} (w : HeightOneSpectrum (𝓞 E)) (B₀ : Multiset ℂˣ) (ν : HChar E) (i : Fin d)
    (hν : ν.IsAbsPow (-spehExp d i + a * spehExp d i)) :
    ((B₀.map (· * ν.val w)).map (· * SatakeVectors.qU w ((modExp (fun _ : Fin d => Fin a) i : ℂ) / 2))).map
      (fun b : ℂˣ => (b : ℂ)) = satTw w (-(spehExp d i : ℂ)) B₀ := by
  rw [SatakeVectors.satTw_eq, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul, SatakeVectors.qU_val, hν.2.1 w, modExp_const]
  rw [mul_assoc, ← Complex.cpow_add _ _ (by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm w).ne_bot)]
  congr 2
  simp only [spehExp]
  push_cast
  ring

omit [IsTotallyComplex E] in

theorem sum_rev {d : ℕ} (w : HeightOneSpectrum (𝓞 E)) (B₀ : Multiset ℂˣ) :
    ∑ i : Fin d, satTw w (-(spehExp d i : ℂ)) B₀ = ∑ i : Fin d, satTw w (spehExp d i : ℂ) B₀ := by
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.revPerm_apply, spehExp_rev]
  push_cast
  ring_nf

end satakeAscent

open satakeAscent in
theorem satAsc_holds : SatAsc := by
  intro E _ _ _ N a d V π hV hA
  obtain ⟨hsum, ν, hν, f, hfP, hfi, hfe⟩ := hA
  filter_upwards [eventually_spherical π] with w hw
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.CuspRep.UnrSat.exists_hasSatGL_locRep PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E a π w hw
  refine ⟨B₀, hB₀, fun B hB => ?_⟩
  obtain ⟨φ, hφV, hφ⟩ := hB.1
  have hF := hfP φ hφV
  have hF0 : f φ ≠ 0 := fun e => hφ.1 (hfi φ hφV e)
  have hFK : ∀ k ∈ GlobalTheory.LFun.KGL w N, finRep E N (locGL E N w k) (f φ) = f φ := fun k hk => by
    have e := hfe (.fin (locGL E N w k)) φ hφV
    have e2 : finRep E N (locGL E N w k) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hφ.2.1 k hk
    exact e.symm.trans (congrArg f e2)
  have hS : ∀ i, SatakeVectors.SatLike (π.twist (ν i)).V w (B₀.map (· * (ν i).val w)) := fun i =>
    satLike_cusp _ (GlobalTheory.SphGal.hasSatGL_twist E a π (ν i) w B₀ ((hν i).1 w) hB₀)
  have hc := SatakeVectors.isSatVecGL_of_ind hsum (fun i => (π.twist (ν i)).V)
    (fun i g ψ hψ => (π.twist (ν i)).stable (.fin g) ψ hψ) (fun i ψ hψ => ((π.twist (ν i)).cusp ψ hψ).1.level.preimage (CuspSub.continuous_locGL w))
    _ hS hF0 hFK hF.1 hF.2.2.2
  have hφ' : GlobalTheory.LFun.IsSatVecGL w (GlobalTheory.DiscLocEx.locRepD hV.stable w) ⟨φ, hφV⟩ B :=
    GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := (finRep E N).comp (locGL E N w)) V.subtype (fun _ _ => rfl)
      Subtype.val_injective hφ
  have hm := hφ'.map (ρ' := (finRep E N).comp (locGL E N w)) (f ∘ₗ V.subtype) (fun g v => hfe (.fin (locGL E N w g)) v.1 v.2) hF0
  rw [hm.unique hc, ← sum_rev, ← Finset.sum_congr rfl fun i _ => term_eq w B₀ (ν i) i (hν i)]
  exact map_sum (Multiset.mapAddMonoidHom fun b : ℂˣ => (b : ℂ)) _ _

end PositivityTheory.Rg.Rs

end
