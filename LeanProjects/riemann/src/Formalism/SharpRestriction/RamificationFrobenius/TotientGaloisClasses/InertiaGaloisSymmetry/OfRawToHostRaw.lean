import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CycAll
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.Imports
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.DvdDiscrOfInertia

noncomputable section

namespace Formalism.HC

theorem HostRaw.der {φ : Frame} (H : HostRaw φ) : HostDer H :=
  have C := Der.hostCore H
  { art_surj := C.art_surj
    cm := C.cm
    conj_iff := C.conj_iff
    finrank_E := C.finrank_E
    finrank_F := C.finrank_F
    mem_F := C.mem_F
    cmType := Der.cmType H
    ps_root := Der.ps_root H
    art_ch := C.art_ch
    ps_d := C.ps_d
    frob := C.frob
    frob_any := C.frob_any
    inertia := C.inertia
    decomp := C.decomp
    inertia_d := C.inertia_d
    decomp_typeI := C.decomp_typeI
    decompConj := C.decompConj
    unramEF := C.unramEF
    splitK := Der.splitK H
    ordinary := Der.ordinary H C
    eta := Der.eta H C
    diffSupport := Der.diffSupport H C
    principal := Der.principal H C
    unimodular := Der.unimodular H
    discr_sq := Der.discr_sq H C
    discr_primes := Der.discr_primes H C
    rd_ge := Der.rd_ge H C
    rd_le := Der.rd_le H
    rd_sq_ge := Der.rd_sq_ge H C
    norm_mu := Der.norm_mu H C }

def HostAx.ofRaw {φ : Frame} (H : HostRaw φ) : HostAx φ := ⟨H, H.der⟩

@[simp] theorem HostAx.ofRaw_toHostRaw {φ : Frame} (H : HostRaw φ) : (HostAx.ofRaw H).toHostRaw = H := rfl

end Formalism.HC

end
